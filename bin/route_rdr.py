#!/usr/bin/env python

# Process RDR2 information from a source (http, https, file) to a destination (analyze display, file, warehouse)
# Can also subscribe from AMQP
#
# TODO:
#  ...
import os
import pwd
import re
import sys
import argparse
import logging
import logging.handlers
import signal
import datetime
from datetime import datetime, tzinfo, timedelta
from time import sleep
try:
    import http.client as httplib
except ImportError:
    import httplib
import json
import ssl
import shutil

import django
django.setup()
from django.db import DataError, IntegrityError
from django.utils.dateparse import parse_datetime
from rdr_db.models import *
from processing_status.process import ProcessingActivity

from daemon import runner
import pdb

class UTC(tzinfo):
    def utcoffset(self, dt):
        return timedelta(0)
    def tzname(self, dt):
        return 'UTC'
    def dst(self, dt):
        return timedelta(0)
utc = UTC()

class HandleRDR():
    def __init__(self):
        self.args = None
        self.config = {}
        self.src = {}
        self.dest = {}
        for var in ['uri', 'scheme', 'path']: # Where <full> contains <type>:<obj>
            self.src[var] = None
            self.dest[var] = None
        self.peak_sleep = 10 * 60        # 10 minutes in seconds during peak business hours
        self.off_sleep = 60 * 60         # 60 minutes in seconds during off hours
        self.max_stale = 24 * 60 * 60    # 24 hours in seconds force refresh
        # These attributes have their own database column
        # Some fields exist in both parent and sub-resources, while others only in one
        # Those in one will be left empty in the other, or inherit from the parent
        self.have_column = ['resource_id', 'info_resourceid',
                            'resource_descriptive_name', 'resource_description',
                            'project_affiliation', 'provider_level',
                            'resource_status', 'current_statuses', 'updated_at']

        default_file = 'file:./rdr.json'

        parser = argparse.ArgumentParser(epilog='File SRC|DEST syntax: file:<file path and name')
        parser.add_argument('daemon_action', nargs='?', choices=('start', 'stop', 'restart'), \
                            help='{start, stop, restart} daemon')
        parser.add_argument('-s', '--source', action='store', dest='src', \
                            help='Messages source {file, http[s]} (default=file)')
#        parser.add_argument('-a', '--subscribe', action='store', dest='sub', \
#                            help='Messages subscribe from AMQP')
        parser.add_argument('-d', '--destination', action='store', dest='dest', \
                            help='Message destination {file, analyze, or warehouse} (default=analyze)')
        parser.add_argument('-l', '--log', action='store', \
                            help='Logging level (default=warning)')
        parser.add_argument('-c', '--config', action='store', default='./route_rdr.conf', \
                            help='Configuration file default=./route_rdr.conf')
        parser.add_argument('--verbose', action='store_true', \
                            help='Verbose output')
        parser.add_argument('--daemon', action='store_true', \
                            help='Daemonize execution')
        parser.add_argument('--pdb', action='store_true', \
                            help='Run with Python debugger')
        self.args = parser.parse_args()

        if self.args.pdb:
            pdb.set_trace()

        # Load configuration file
        config_path = os.path.abspath(self.args.config)
        try:
            with open(config_path, 'r') as file:
                conf=file.read()
                file.close()
        except IOError as e:
            raise
        try:
            self.config = json.loads(conf)
        except ValueError as e:
            print('Error "{}" parsing config={}'.format(e, config_path))
            sys.exit(1)

        # Initialize logging from arguments, or config file, or default to WARNING as last resort
        numeric_log = None
        if self.args.log is not None:
            numeric_log = getattr(logging, self.args.log.upper(), None)
        if numeric_log is None and 'LOG_LEVEL' in self.config:
            numeric_log = getattr(logging, self.config['LOG_LEVEL'].upper(), None)
        if numeric_log is None:
            numeric_log = getattr(logging, 'WARNING', None)
        if not isinstance(numeric_log, int):
            raise ValueError('Invalid log level: {}'.format(numeric_log))
        self.logger = logging.getLogger('DaemonLog')
        self.logger.setLevel(numeric_log)
        self.formatter = logging.Formatter(fmt='%(asctime)s.%(msecs)03d %(levelname)s %(message)s', \
                                           datefmt='%Y/%m/%d %H:%M:%S')
        self.handler = logging.handlers.TimedRotatingFileHandler(self.config['LOG_FILE'], when='W6', \
                                                                 backupCount=999, utc=True)
        self.handler.setFormatter(self.formatter)
        self.logger.addHandler(self.handler)

        # Verify arguments and parse compound arguments
        if not getattr(self.args, 'src', None): # Tests for None and empty ''
            if 'RDR_INFO_URL' in self.config:
                self.args.src = self.config['RDR_INFO_URL']
        if not getattr(self.args, 'src', None): # Tests for None and empty ''
            self.args.src = default_file
        idx = self.args.src.find(':')
        if idx > 0:
            (self.src['scheme'], self.src['path']) = (self.args.src[0:idx], self.args.src[idx+1:])
        else:
            (self.src['scheme'], self.src['path']) = (self.args.src, None)
        if self.src['scheme'] not in ['file', 'http', 'https']:
            self.logger.error('Source not {file, http, https}')
            sys.exit(1)
        if self.src['scheme'] in ['http', 'https']:
            if self.src['path'][0:2] != '//':
                self.logger.error('Source URL not followed by "//"')
                sys.exit(1)
            self.src['path'] = self.src['path'][2:]
        self.src['uri'] = self.args.src

        if not getattr(self.args, 'dest', None): # Tests for None and empty ''
            if 'DESTINATION' in self.config:
                self.args.dest = self.config['DESTINATION']
        if not getattr(self.args, 'dest', None): # Tests for None and empty ''
            self.args.dest = 'analyze'
        idx = self.args.dest.find(':')
        if idx > 0:
            (self.dest['scheme'], self.dest['path']) = (self.args.dest[0:idx], self.args.dest[idx+1:])
        else:
            self.dest['scheme'] = self.args.dest
        if self.dest['scheme'] not in ['file', 'analyze', 'warehouse']:
            self.logger.error('Destination not {file, analyze, warehouse}')
            sys.exit(1)
        self.dest['uri'] = self.args.dest

        if self.src['scheme'] in ['file'] and self.dest['scheme'] in ['file']:
            self.logger.error('Source and Destination can not both be a {file}')
            sys.exit(1)

        if self.args.daemon_action:
            self.stdin_path = '/dev/null'
            if 'LOG_FILE' in self.config:
                self.stdout_path = self.config['LOG_FILE'].replace('.log', '.daemon.log')
                self.stderr_path = self.stdout_path
            else:
                self.stdout_path = '/dev/tty'
                self.stderr_path = '/dev/tty'
            self.SaveDaemonLog(self.stdout_path)
            self.pidfile_timeout = 5
            if 'PID_FILE' in self.config:
                self.pidfile_path =  self.config['PID_FILE']
            else:
                name = os.path.basename(__file__).replace('.py', '')
                self.pidfile_path =  '/var/run/{}/{}.pid'.format(name ,name)

    def Retrieve_RDR(self, url):
        idx = url.find(':')
        if idx <= 0:
            self.logger.error('Retrieve URL is not valid')
            sys.exit(1)
            
        (type, obj) = (url[0:idx], url[idx+1:])
        if type not in ['http', 'https']:
            self.logger.error('Retrieve URL is not valid')
            sys.exit(1)

        if obj[0:2] != '//':
            self.logger.error('Retrieve URL is not valid')
            sys.exit(1)
            
        obj = obj[2:]
        idx = obj.find('/')
        if idx <= 0:
            self.logger.error('Retrieve URL is not valid')
            sys.exit(1)

        (host, path) = (obj[0:idx], obj[idx:])
        idx = host.find(':')
        if idx > 0:
            port = host[idx+1:]
        elif type == 'https':
            port = '443'
        else:
            port = '80'
        
        headers = {'Content-type': 'application/json',
                    'XA-CLIENT': 'XSEDE',
                    'XA-KEY-FORMAT': 'underscore'}
        ctx = ssl.create_default_context(ssl.Purpose.CLIENT_AUTH)
        conn = httplib.HTTPSConnection(host=host, port=port, context=ctx)
        if path[0] != '/':
            path = '/' + path
        conn.request('GET', path, None , headers)
        self.logger.debug('HTTP GET  {}'.format(url))
        response = conn.getresponse()
        result = response.read()
        self.logger.debug('HTTP RESP {} {} (returned {}/bytes)'.format(response.status, response.reason, len(result)))
        try:
            rdr_obj = json.loads(result)
        except ValueError as e:
            self.logger.error('Response not in expected JSON format ({})'.format(e))
            return(None)
        else:
            return(rdr_obj)

    def Analyze_RDR(self, rdr_obj):
        if 'resources' not in rdr_obj:
            self.logger.error('RDR JSON response is missing the base \'resources\' element')
            self.stats['Skip'] += 1
            sys.exit(1)
        maxlen = {}
        for p_res in rdr_obj['resources']:  # Parent resources
            if any(x not in p_res for x in ('project_affiliation', 'resource_id', 'info_resourceid')) \
                    or p_res['project_affiliation'] != 'XSEDE' \
                    or str(p_res['info_resourceid']).lower() == 'none' \
                    or p_res['info_resourceid'] == '':
                self.stats['Skip'] += 1
                continue
            self.stats['Update'] += 1
            self.logger.info('ID={}, ResourceID={}, Level="{}", Description="{}"'.format(p_res['resource_id'], p_res['info_resourceid'], p_res['provider_level'], p_res['resource_descriptive_name']))
            
            self.sub = {}   # Sub-resource attributes go here
            for subtype in ['compute_resources', 'storage_resources', 'grid_resources', 'other_resources']:
                if subtype in p_res:
                    self.sub[subtype]=p_res[subtype]
            
            for x in p_res:
                if isinstance(p_res[x], dict):
                    msg='dict({})'.format(len(p_res[x]))
                elif isinstance(p_res[x], list):
                    msg='list({})'.format(len(p_res[x]))
                else:
                    msg=u'"{}"'.format(p_res[x])
                if x in self.have_column:
                    try:
                        if x not in maxlen or (x in maxlen and maxlen[x] <= len(p_res[x])):
                            maxlen[x] = len(p_res[x])
                    except:
                        pass
                self.logger.debug(u'  {}={}'.format(x, msg))
            
        for subtype in self.sub:
            for s_res in self.sub[subtype]: # Sub resources
                for x in s_res:
                    if x in self.have_column:
                        try:
                            if x not in maxlen or (x in maxlen and maxlen[x] <= len(s_res[x])):
                                maxlen[x] = len(s_res[x])
                        except:
                            pass

        for x in maxlen:
            self.logger.debug('Max({})={}'.format(x, maxlen[x]))

    def Write_Cache(self, file, rdr_obj):
        data = json.dumps(rdr_obj)
        with open(file, 'w') as my_file:
            my_file.write(data)
            my_file.close()
        self.logger.info('Serialized and wrote {} bytes to file={}'.format(len(data), file))
        return(len(data))

    def Read_Cache(self, file):
        with open(file, 'r') as my_file:
            data = my_file.read()
            my_file.close()
        try:
            rdr_obj = json.loads(data)
            self.logger.info('Read and parsed {} bytes from file={}'.format(len(data), file))
            return(rdr_obj)
        except ValueError as e:
            self.logger.error('Error "{}" parsing file={}'.format(e, file))
            sys.exit(1)

    def Warehouse_RDR(self, rdr_obj):
        if 'resources' not in rdr_obj:
            self.stats['Skip'] += 1
            msg = 'RDR JSON response is missing a \'resources\' element'
            self.logger.error(msg)
            return(False, msg)

        id_lookup = {'compute_resources':   'compute_resource_id',
                    'other_resources':     'other_resource_id',
                    'grid_resources':      'grid_resource_id',
                    'storage_resources':   'storage_resource_id',
                }
        type_lookup = {'compute_resources': 'compute',
                    'other_resources':     'other',
                    'grid_resources':      'grid',
                    'storage_resources':   'storage',
                }

        self.cur = {}   # Resources currently in database
        self.new = {}   # New resources in document
        for item in RDRResource.objects.all():
            self.cur[item.rdr_resource_id] = item

        for p_res in rdr_obj['resources']:
            # Require affiliation=XSEDE, a resource_id, and an information services ResourceID
            if any(x not in p_res for x in ('project_affiliation', 'resource_id', 'info_resourceid')) \
                    or p_res['project_affiliation'] != 'XSEDE' \
                    or str(p_res['info_resourceid']).lower() == 'none' \
                    or p_res['info_resourceid'] == '':
                self.stats['Skip'] += 1
                continue

            # Attributes that don't have their own model field get put in the other_attributes field
            other_attributes=p_res.copy()
            self.sub = {}   # Sub-resource attributes go here
            for subtype in ['compute_resources', 'storage_resources', 'grid_resources', 'other_resources']:
                if subtype in p_res:
                    self.sub[subtype]=p_res[subtype]
                    other_attributes.pop(subtype, None)
            for attrib in self.have_column:
                other_attributes.pop(attrib, None)

            p_latest_status = self.latest_status(p_res['current_statuses'])
            try:
                model = RDRResource(rdr_resource_id=p_res['resource_id'],
                                    info_resourceid=p_res['info_resourceid'],
                                    info_siteid=p_res['info_resourceid'][p_res['info_resourceid'].find('.')+1:],
                                    rdr_type='resource',
                                    resource_descriptive_name=p_res['resource_descriptive_name'],
                                    resource_description=p_res['resource_description'],
                                    resource_status=p_res['resource_status'],
                                    current_statuses=', '.join(p_res['current_statuses']),
                                    latest_status=p_latest_status,
                                    latest_status_begin=self.latest_status_date(p_res['resource_status'], p_latest_status, 'begin'),
                                    latest_status_end=self.latest_status_date(p_res['resource_status'], p_latest_status, 'end'),
                                    parent_resource=None,
                                    recommended_use=None,
                                    access_description=None,
                                    project_affiliation=p_res['project_affiliation'],
                                    provider_level=p_res['provider_level'],
                                    other_attributes=other_attributes,
                                    updated_at=p_res['updated_at'],
                                    )
                model.save()
                self.logger.debug('Base ID={}, ResourceID={}'.format(p_res['resource_id'], p_res['info_resourceid']))
                self.new[p_res['resource_id']]=model
                self.stats['Update'] += 1
            except (DataError, IntegrityError) as e:
                msg = '{} saving resource_id={} ({}): {}'.format(type(e).__name__, p_res['resource_id'], p_res['info_resourceid'], e.message)
                self.logger.error(msg)
                return(False, msg)

            for subtype in self.sub:
                for s_res in self.sub[subtype]:
                    other_attributes=s_res.copy()
                    for attrib in [id_lookup[subtype], 'info_resourceid', 'parent_resource',
                              'resource_descriptive_name', 'resource_description', 'access_description',
                              'recommended_use', 'resource_status', 'current_statuses', 'updated_at']:
                        other_attributes.pop(attrib, None)
                    s_latest_status = self.latest_status(s_res['current_statuses'])
                    try:
                        model = RDRResource(rdr_resource_id=s_res[id_lookup[subtype]],
                                            info_resourceid=s_res['info_resourceid'],
                                            info_siteid=s_res['info_resourceid'][s_res['info_resourceid'].find('.')+1:],
                                            rdr_type=type_lookup[subtype],
                                            resource_descriptive_name=s_res['resource_descriptive_name'],
                                            resource_description=s_res['resource_description'],
                                            resource_status=s_res['resource_status'],
                                            current_statuses=', '.join(s_res['current_statuses']),
                                            latest_status=s_latest_status,
                                            latest_status_begin=self.latest_status_date(s_res['resource_status'], s_latest_status, 'begin'),
                                            latest_status_end=self.latest_status_date(s_res['resource_status'], s_latest_status, 'end'),
                                            parent_resource=s_res['parent_resource']['resource_id'],
                                            recommended_use=s_res['recommended_use'],
                                            access_description=s_res['access_description'],
                                            project_affiliation=s_res.get('project_affiliation', p_res['project_affiliation']),
                                            provider_level=s_res.get('provider_level', p_res['provider_level']),
                                            other_attributes=other_attributes,
                                            updated_at=s_res['updated_at'],
                                            )
                        model.save()
                        self.logger.debug(' Sub ID={}, ResourceID={}, Type={}'.format(s_res[id_lookup[subtype]], s_res['parent_resource']['info_resourceid'], type_lookup[subtype]))
                        self.new[s_res[id_lookup[subtype]]]=model
                        self.stats['Update'] += 1
                    except (DataError, IntegrityError) as e:
                        msg = '{} saving resource_id={} ({}): {}'.format(type(e).__name__, s_res[id_lookup[subtype]], s_res['info_resourceid'], e.message)
                        self.logger.error(msg)
                        return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    RDRResource.objects.filter(rdr_resource_id=id).delete()
                    self.stats['Delete'] += 1
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e.message))
        return(True, '')
            
    def latest_status(self, current_statuses):
        for ordered_status in ['decommissioned', 'retired', 'post_production', 'production', 'pre_production', 'friendly', 'coming_soon']:
            if ordered_status in current_statuses:
                return(ordered_status)
        if len(current_statuses) > 0:
           return(current_statuses[0])
        else:
           return('')

    def latest_status_date(self, resource_status_dates, current_status, which_date):
        # which should be 'begin' or 'end'
        fixed_current_status = current_status.replace('-', '_')
        key = '{}_{}_date'.format(fixed_current_status, which_date)
        if key not in resource_status_dates or resource_status_dates[key] is None:
            return(None)
        try:
            return(datetime.strptime(resource_status_dates[key], "%Y-%m-%d"))
        except:
            return(None)

    def SaveDaemonLog(self, path):
        # Save daemon log file using timestamp only if it has anything unexpected in it
        try:
            with open(path, 'r') as file:
                lines=file.read()
                file.close()
                if not re.match("^started with pid \d+$", lines) and not re.match("^$", lines):
                    ts = datetime.strftime(datetime.now(), '%Y-%m-%d_%H:%M:%S')
                    newpath = '{}.{}'.format(path, ts)
                    shutil.copy(path, newpath)
                    print('SaveDaemonLog as {}'.format(newpath))
        except Exception as e:
            print('Exception in SaveDaemonLog({})'.format(path))
        return

    def exit_signal(self, signal, frame):
        self.logger.critical('Caught signal={}, exiting...'.format(signal))
        sys.exit(0)

    def smart_sleep(self, last_run):
        # This functions sleeps, performs refresh checks, and returns when it's time to refresh
        while True:
            if 12 <= datetime.now(utc).hour <= 24: # Between 6 AM and 6 PM Central (~12 to 24 UTC)
                current_sleep = self.peak_sleep
            else:
                current_sleep = self.off_sleep
            self.logger.debug('sleep({})'.format(current_sleep))
            sleep(current_sleep)

            # Force a refresh every 12 hours at Noon and Midnight UTC
            now_utc = datetime.now(utc)
            if ( (now_utc.hour < 12 and last_run.hour > 12) or \
                (now_utc.hour > 12 and last_run.hour < 12) ):
                self.logger.info('REFRESH TRIGGER: Every 12 hours')
                return

            # Force a refresh every max_stale seconds
            since_last_run = now_utc - last_run
            if since_last_run.seconds > self.max_stale:
                self.logger.info('REFRESH TRIGGER: Stale {}/seconds above thresdhold of {}/seconds'.format(since_last_run.seconds, self.max_stale) )
                return

            # If recent database update
            if 'RDR_LAST_URL' in self.config and self.config['RDR_LAST_URL']:
                ts_json = self.Retrieve_RDR(self.config['RDR_LAST_URL'])
            try:
                last_db_update = parse_datetime(ts_json['last_update_time'])
                self.logger.info('Last DB update at {} with last refresh at {}'.format(last_db_update, last_run))
                if last_db_update > last_run:
                    self.logger.info('REFRESH TRIGGER: DB update since last run')
                    return
            except Exception as e:
                self.logger.error('{} parsing last_update_time={}: {}'.format(type(e).__name__, ts_json['last_update_time'], e.message))
                last_db_update = None

    def run(self):
        signal.signal(signal.SIGINT, self.exit_signal)
        signal.signal(signal.SIGTERM, self.exit_signal)
        self.logger.info('Starting program={} pid={}, uid={}({})'.format(os.path.basename(__file__), os.getpid(), os.geteuid(), pwd.getpwuid(os.geteuid()).pw_name))

        while True:
            self.start = datetime.now(utc)
            self.stats = {
                'Update': 0,
                'Delete': 0,
                'Skip': 0,
            }
            
            if self.src['scheme'] == 'file':
                RDR = self.Read_Cache(self.src['path'])
            else:
                RDR = self.Retrieve_RDR(self.src['uri'])

            if self.dest['scheme'] == 'file':
                bytes = self.Write_Cache(self.dest['path'], RDR)
            elif self.dest['scheme'] == 'analyze':
                self.Analyze_RDR(RDR)
            elif self.dest['scheme'] == 'warehouse':
                pa_application=os.path.basename(__file__)
                pa_function='Warehouse_RDR'
#                pa_id = self.src['uri']
                pa_id = 'rdr'
                pa_topic = 'rdr'
                pa_about = 'xsede.org'
                pa = ProcessingActivity(pa_application, pa_function, pa_id , pa_topic, pa_about)
                (rc, warehouse_msg) = self.Warehouse_RDR(RDR)
            
            self.end = datetime.now(utc)
            summary_msg = 'Processed in {:.3f}/seconds: {}/updates, {}/deletes, {}/skipped'.format((self.end - self.start).total_seconds(), self.stats['Update'], self.stats['Delete'], self.stats['Skip'])
            self.logger.info(summary_msg)
            if self.dest['scheme'] == 'warehouse':
                if rc:  # No errors
                    pa.FinishActivity(rc, summary_msg)
                else:   # Something failed, use returned message
                    pa.FinishActivity(rc, warehouse_msg)
            if not self.args.daemon_action:
                break
            self.smart_sleep(self.start)

if __name__ == '__main__':
    router = HandleRDR()
    if router.args.daemon_action is None:  # Interactive execution
        myrouter = router.run()
        sys.exit(0)
    
    if router.args.daemon_action == 'start':
        if router.src['scheme'] not in ['http', 'https'] or router.dest['scheme'] not in ['warehouse']:
            router.logger.error('Can only daemonize when source=[http|https] and destination=warehouse')
            sys.exit(1)

    # Daemon execution
    router.logger.info('Daemon startup')
    daemon_runner = runner.DaemonRunner(router)
    daemon_runner.daemon_context.files_preserve=[router.handler.stream]
    daemon_runner.daemon_context.working_directory=router.config['RUN_DIR']
    daemon_runner.do_action()
