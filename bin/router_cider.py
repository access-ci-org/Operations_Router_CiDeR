#!/usr/bin/env python3

import argparse
from collections import Counter
from datetime import datetime, timezone
import http.client as httplib
import json
import logging
import logging.handlers
import os
from pid import PidFile
import pwd
import re
import sys
import shutil
import signal
import ssl
from time import sleep
import traceback
from urllib.parse import urlparse, urlunparse, urljoin

import django
django.setup()
from django.db import DataError, IntegrityError
from django.conf import settings
from django.utils.dateparse import parse_datetime
from cider.models import *
from warehouse_state.process import ProcessingActivity

import pdb

# Used during initialization before loggin is enabled
def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

class Router():
    def __init__(self):
        parser = argparse.ArgumentParser(epilog='File SRC|DEST syntax: file:<file path and name')
        parser.add_argument('--once', action='store_true', help='Run once and exit, or run continuous with sleep between interations (default)')
        parser.add_argument('--daemon', action='store_true', help='Daemonize execution')
        parser.add_argument('-s', '--source', action='store', dest='src', help='Messages source {file, http[s]} (default=file)')
        parser.add_argument('-d', '--destination', action='store', dest='dest', help='Message destination {file, analyze, or warehouse} (default=analyze)')
        parser.add_argument('-l', '--log', action='store', help='Logging level (default=warning)')
        parser.add_argument('-c', '--config', action='store', default='./router_cider.conf', help='Configuration file default=./router_cider.conf')
        parser.add_argument('--pdb', action='store_true', help='Run with Python debugger')
        self.args = parser.parse_args()

        # Trace for debugging as early as possible
        if self.args.pdb:
            pdb.set_trace()

        # Load configuration file
        self.config_file = os.path.abspath(self.args.config)
        try:
            with open(self.config_file, 'r') as file:
                conf=file.read()
        except IOError as e:
            eprint('Error "{}" reading config={}'.format(e, self.config_file))
            sys.exit(1)
        try:
            self.config = json.loads(conf)
        except ValueError as e:
            eprint('Error "{}" parsing config={}'.format(e, self.config_file))
            sys.exit(1)

        if self.config.get('PID_FILE'):
            self.pidfile_path =  self.config['PID_FILE']
        else:
            name = os.path.basename(__file__).replace('.py', '')
            self.pidfile_path = '/var/run/{}/{}.pid'.format(name, name)

    def Setup(self):
        # Initialize log level from arguments, or config file, or default to WARNING
        loglevel_str = (self.args.log or self.config.get('LOG_LEVEL', 'WARNING')).upper()
        loglevel_num = getattr(logging, loglevel_str, None)
        self.logger = logging.getLogger('DaemonLog')
        self.logger.setLevel(loglevel_num)
        self.formatter = logging.Formatter(fmt='%(asctime)s.%(msecs)03d %(levelname)s %(message)s', datefmt='%Y/%m/%d %H:%M:%S')
        self.handler = logging.handlers.TimedRotatingFileHandler(self.config['LOG_FILE'], when='W6', backupCount=999, utc=True)
        self.handler.setFormatter(self.formatter)
        self.logger.addHandler(self.handler)

        # Initialize stdout, stderr
        if self.args.daemon and 'LOG_FILE' in self.config:
            self.stdout_path = self.config['LOG_FILE'].replace('.log', '.daemon.log')
            self.stderr_path = self.stdout_path
            self.SaveDaemonStdOut(self.stdout_path)
            sys.stdout = open(self.stdout_path, 'wt+')
            sys.stderr = open(self.stderr_path, 'wt+')

        signal.signal(signal.SIGINT, self.exit_signal)
        signal.signal(signal.SIGTERM, self.exit_signal)

        self.logger.info('Starting program={} pid={}, uid={}({})'.format(os.path.basename(__file__),
            os.getpid(), os.geteuid(), pwd.getpwuid(os.geteuid()).pw_name))

        self.dest = {}
        self.peak_sleep = 10 * 60        # 10 minutes in seconds during peak business hours
        self.off_sleep = 60 * 60         # 60 minutes in seconds during off hours
        self.max_stale = 24 * 60 * 60    # 24 hours in seconds force refresh
        src_default = 'file:./cider_infrastructure.json'
        dest_default = 'analyze'

        # Verify arguments and parse compound arguments
        if not getattr(self.args, 'src', None): # Tests for None and empty ''
            if 'CIDER_INFO_URL' in self.config:
                self.args.src = self.config['CIDER_INFO_URL']
        if not getattr(self.args, 'src', None): # Tests for None and empty '', CIDER_INFO_URL could be defined but empty
            self.args.src = src_default
        self.srcparsed = urlparse(self.args.src)
        if self.srcparsed.scheme not in ['file', 'http', 'https']:
            self.logger.error('Source not {file, http, https}')
            sys.exit(1)
        self.srcdisplay = urlunparse(self.srcparsed)

        if not getattr(self.args, 'dest', None): # Tests for None and empty ''
            if 'DESTINATION' in self.config:
                self.args.dest = self.config['DESTINATION']
        if not getattr(self.args, 'dest', None): # Tests for None and empty '', DESTINATION could be defined but empty
            self.args.dest = dest_default
        idx = self.args.dest.find(':')
        if idx > 0:
            (self.dest['scheme'], self.dest['path']) = (self.args.dest[0:idx], self.args.dest[idx+1:])
        else:
            self.dest['scheme'] = self.args.dest
        if self.dest['scheme'] not in ['file', 'analyze', 'warehouse']:
            self.logger.error('Destination not {file, analyze, warehouse}')
            sys.exit(1)
        self.dest['uri'] = self.args.dest
        if self.dest['scheme'] == 'warehouse':
            self.destdisplay = '{}@database={}'.format(self.dest['scheme'], settings.DATABASES['default']['HOST'])
        else:
            self.destdisplay = self.args.dest

        if self.srcparsed.scheme in ['file'] and self.dest['scheme'] in ['file']:
            self.logger.error('Source and Destination can not both be a {file}')
            sys.exit(1)
        
        # The affiliations we are processing
        self.AFFILIATIONS = set(self.config.get('AFFILIATIONS', ['ACCESS']))
        
        if self.srcparsed.scheme not in ['http', 'https'] or self.dest['scheme'] not in ['warehouse']:
            self.logger.error('Can only daemonize when source=[http|https] and destination=warehouse')
            sys.exit(1)

        # If path to the CiDeR last update API is set, use it to determine if there are resource updates
        if self.srcparsed.scheme in ['http', 'https'] and self.config.get('CIDER_LAST_PATH'):
            self.lasturldisplay = urljoin(urlunparse(self.srcparsed), self.config.get('CIDER_LAST_PATH'))
            self.lasturl = urlparse(self.lasturldisplay)
        if self.srcparsed.scheme in ['http', 'https'] and self.config.get('CIDER_FEATURES_PATH'):
            self.featuresurldisplay = urljoin(urlunparse(self.srcparsed), self.config.get('CIDER_FEATURES_PATH'))
            self.featuresurl = urlparse(self.featuresurldisplay)
        if self.srcparsed.scheme in ['http', 'https'] and self.config.get('CIDER_GROUPS_PATH'):
            self.groupsurldisplay = urljoin(urlunparse(self.srcparsed), self.config.get('CIDER_GROUPS_PATH'))
            self.groupsurl = urlparse(self.groupsurldisplay)

        self.logger.info('Source: {}'.format(self.srcdisplay))
        self.logger.info('Destination: {}'.format(self.destdisplay))
        if hasattr(self, 'lasturldisplay'): self.logger.info('Last URL: {}'.format(self.lasturldisplay))
        if hasattr(self, 'featuresurldisplay'): self.logger.info('Features URL: {}'.format(self.featuresurldisplay))
        if hasattr(self, 'groupsurldisplay'): self.logger.info('Groups URL: {}'.format(self.groupsurldisplay))
        self.logger.info('Config: {}' .format(self.config_file))
        self.logger.info('Log Level: {}({})'.format(loglevel_str, loglevel_num))
        self.logger.info('Affiliations: ' + ', '.join(self.AFFILIATIONS))

        # These attributes have their own database column
        self.resource_model_fields = ['resource_id', 'info_resourceid', 'resource_type'
                        'resource_descriptive_name', 'resource_description',
                        'project_affiliation', 'provider_level',
                        'resource_status', 'current_statuses', 'updated_at']
        self.feature_model_fields = ['id', 'name', 'description',
                        'features']
        self.group_model_fields = ['info_groupid', 'name', 'description',
                        'group_logo_url', 'group_types', 'info_resourceids']

    def SaveDaemonStdOut(self, path):
        # Save daemon log file using timestamp only if it has anything unexpected in it
        try:
            file = open(path, 'r')
            lines = file.read()
            file.close()
            if not re.match("^started with pid \d+$", lines) and not re.match("^$", lines):
                ts = datetime.strftime(datetime.now(), '%Y-%m-%d_%H:%M:%S')
                newpath = '{}.{}'.format(path, ts)
                self.logger.debug('Saving previous daemon stdout to {}'.format(newpath))
                shutil.copy(path, newpath)
        except Exception as e:
            self.logger.error('Exception in SaveDaemonStdOut({})'.format(path))
        return

    def exit_signal(self, signum, frame):
        self.logger.critical('Caught signal={}({}), exiting with rc={}'.format(signum, signal.Signals(signum).name, signum))
        sys.exit(signum)

    def exit(self, rc):
        if rc:
            self.logger.error('Exiting with rc={}'.format(rc))
        sys.exit(rc)

    def Retrieve_Infrastructure(self, parsedurl):
        # The affiliations for a resource compiled at load time
        self.resource_AFFILIATIONS = {}

        infra_all = []
        for AFF in self.AFFILIATIONS:
            infra_aff = self.Retrieve_CiDeR_by_Affiliation(parsedurl, affiliation=AFF)
            if not infra_aff:
                continue
            if 'resources' not in infra_aff:
                self.logger.error('CiDeR JSON response for affiliation={} is missing a \'resources\' element'.format(AFF))
                continue
            self.logger.debug('Retrieved affiliation={} {}/items'.format(AFF, len(infra_aff['resources'])))
            for item in infra_aff['resources']:
                # Collapses multiple occurances of a resource into one resource and accumulate its affiliations
                id = item['resource_id']
                if id in self.resource_AFFILIATIONS:
                    self.resource_AFFILIATIONS[id].add(AFF)
                    continue
                # First occurence of a resource, add it to the infra_all results
                self.resource_AFFILIATIONS[id] = set([AFF])
                infra_all.append(item)
        self.logger.debug('Retrieved from all affiliations {}/items'.format(len(infra_all)))
        return(infra_all)
    
    def Retrieve_CiDeR_by_Affiliation(self, parsedurl, affiliation='ACCESS'):
        if not parsedurl.scheme or not parsedurl.netloc or not parsedurl.path:
            self.logger.error('CiDeR URL is not valid: {}'.format(url))
            sys.exit(1)
        if parsedurl.scheme not in ['http', 'https']:
            self.logger.error('CiDeR URL scheme is not valid: {}'.format(url))
            sys.exit(1)
        port = parsedurl.port or '80' if parsedurl.scheme == 'http' else '443'     # Default is HTTPS/443
        headers = {'Content-type': 'application/json',
                    'XA-CLIENT': affiliation,
                    'XA-KEY-FORMAT': 'underscore'}
#        ctx = ssl.create_default_context(ssl.Purpose.CLIENT_AUTH)
#   2022-10-21 JP - figure out later the appropriate level of ssl verification
        ctx = ssl.create_default_context()
        ctx = ssl._create_unverified_context()
        conn = httplib.HTTPSConnection(host=parsedurl.netloc, port=port, context=ctx)
        conn.request('GET', parsedurl.path, None , headers)
        self.logger.debug('HTTP GET {}'.format(parsedurl.path))
        response = conn.getresponse()
        result = response.read()
        self.logger.debug('HTTP RESP {} {} (returned {}/bytes)'.format(response.status, response.reason, len(result)))
        try:
            result_json = json.loads(result)
        except ValueError as e:
            self.logger.error('Response not in expected JSON format ({})'.format(e))
            return(None)
        return(result_json)

    def Analyze_Info(self, info_json):
        maxlen = {}
        for p_res in info_json:  # Iterating over resources
            # Require affiliation, a resource_id, and an information services ResourceID
            if any(x not in p_res for x in ('project_affiliation', 'resource_id', 'info_resourceid')) \
                    or str(p_res['info_resourceid']).lower() == 'none' \
                    or p_res['info_resourceid'] == '':
                self.RCOUNTERS.update({'Skip'})
                continue
            id = p_res['resource_id']
            affiliations = self.resource_AFFILIATIONS[id]
            if not affiliations & self.AFFILIATIONS: # Intersection
                self.RCOUNTERS.update({'Skip'})
                continue

            self.RCOUNTERS.update({'Update'})
            self.logger.info('ID={}, ResourceID={}, Level="{}", Description="{}"'.format(id, p_res['info_resourceid'], p_res['provider_level'], p_res['resource_descriptive_name']))
            
            for x in p_res:
                if isinstance(p_res[x], dict):
                    msg='dict({})'.format(len(p_res[x]))
                elif isinstance(p_res[x], list):
                    msg='list({})'.format(len(p_res[x]))
                else:
                    msg=u'"{}"'.format(p_res[x])
                if x in self.resource_model_fields:
                    try:
                        if x not in maxlen or (x in maxlen and maxlen[x] <= len(p_res[x])):
                            maxlen[x] = len(p_res[x])
                    except:
                        pass
                self.logger.debug(u'  {}={}'.format(x, msg))
            
        for x in maxlen:
            self.logger.debug('Max({})={}'.format(x, maxlen[x]))

    def Write_Cache(self, file, info_json):
        data = json.dumps(info_json)
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
            info_json = json.loads(data)
            self.logger.info('Read and parsed {} bytes from file={}'.format(len(data), file))
            return(info_json)
        except ValueError as e:
            self.logger.error('Error "{}" parsing file={}'.format(e, file))
            sys.exit(1)

    def Warehouse_Resources(self, info_json):
        type_id_lookup = {
            'Compute': 'compute_resource_id',
            'Storage':    'storage_resource_id',
            'Other':      'other_resource_id',
            'Grid':       'grid_resource_id',
            'Online Service': 'online_service_resource_id',
            'Science Gateway': 'science_gateway_resource_id',
        }

        self.cur = {}   # Resources currently in database
        self.new = {}   # New resources in document
        for item in CiderInfrastructure.objects.all():
            self.cur[item.cider_resource_id] = item
        self.logger.debug('Retrieved from database {}/resources'.format(len(self.cur)))

        for p_res in info_json:  # Iterating over resources
            # Require fields
            if any(x not in p_res for x in ('project_affiliation', 'resource_id', 'info_resourceid')) \
                    or str(p_res['info_resourceid']).lower() == 'none' \
                    or p_res['info_resourceid'] == '':
                self.RCOUNTERS.update({'Skip'})
                continue
            id = p_res['resource_id']
            affiliations = self.resource_AFFILIATIONS[id]
            if not affiliations & self.AFFILIATIONS: # Intersection
                self.RCOUNTERS.update({'Skip'})
                continue
                            
            p_parent_resource_id = p_res['parent_resource'].get('resource_id') if 'parent_resource' in p_res else None
            p_parent_info_resourceid = p_res['parent_resource'].get('info_resourceid') if 'parent_resource' in p_res else None
            
            p_info_resourceid = p_res['info_resourceid']
            #### TEMPORARY JP 2023-11-08 ####
            if len(p_info_resourceid) > 40 and p_parent_info_resourceid:
                p_info_resourceid = p_parent_info_resourceid
                self.logger.error('CiDeR bug for ID={} replacing len(info_resourceid)>40 with parent "{}"'.format(id, p_parent_info_resourceid))

            p_latest_status = self.latest_status(p_res['current_statuses'])
            
            p_info_siteid = p_info_resourceid[p_info_resourceid.find('.')+1:]
            #### TEMPORARY JP 2023-11-08 ####
            if len(p_info_siteid) > 40 and p_parent_info_resourceid:
                p_info_siteid = p_parent_info_resourceid[p_parent_info_resourceid.find('.')+1:]
                self.logger.error('CiDeR bug for ID={} replacing len(info_siteid)>40 with parent derived "{}"'.format(id, p_info_siteid))
                
            # All the attributes, then remove the ones that have their own field
            other_attributes=p_res.copy()
            for attrib in self.resource_model_fields:
                other_attributes.pop(attrib, None)

            try:
                model, created = CiderInfrastructure.objects.update_or_create(
                                    cider_resource_id=id,
                                    defaults = {
                                        'info_resourceid': p_info_resourceid,
                                        'info_siteid': p_info_siteid,
                                        'cider_type': p_res['resource_type'],
                                        'resource_descriptive_name': p_res['resource_descriptive_name'],
                                        'resource_description': p_res['resource_description'],
                                        'resource_status': p_res['resource_status'],
                                        'current_statuses': ', '.join(p_res['current_statuses']),
                                        'latest_status': p_latest_status,
                                        'latest_status_begin': self.latest_status_date(p_res['resource_status'], p_latest_status, 'begin'),
                                        'latest_status_end': self.latest_status_date(p_res['resource_status'], p_latest_status, 'end'),
                                        'parent_resource': p_parent_resource_id,
                                        'recommended_use': p_res.get('recommended_use'),
                                        'access_description': p_res.get('access_description'),
                                        'project_affiliation': ','.join(affiliations),
                                        'provider_level': p_res['provider_level'],
                                        'other_attributes': other_attributes,
                                        'updated_at': p_res['updated_at']
                                    })
                model.save()
                self.logger.debug('Base ID={}, ResourceID={}, created={}'.format(id, p_info_resourceid, created))
                self.new[id]=model
                self.RCOUNTERS.update({'Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={} ({}): {}'.format(type(e).__name__, id, p_info_resourceid, str(e))
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    CiderInfrastructure.objects.filter(cider_resource_id=id).delete()
                    self.RCOUNTERS.update({'Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, str(e)))
        return(True, '')
            
    def Warehouse_Features(self, info_json):
        self.cur = {}   # Feature categories currently in database
        self.new = {}   # New feature categories in document
        for item in CiderFeatures.objects.all():
            self.cur[item.feature_category_id] = item
        self.logger.debug('Retrieved from database {}/feature categories'.format(len(self.cur)))

        for p_feat in info_json['feature_categories']:  # Iterating over feature groups
            id = p_feat['feature_category_id']
            # All the attributes, then remove the ones that have their own field
            other_attributes=p_feat.copy()
            for attrib in self.feature_model_fields:
                other_attributes.pop(attrib, None)

            try:
                model, created = CiderFeatures.objects.update_or_create(
                                    feature_category_id=id,
                                    defaults = {
                                        'feature_category_name': p_feat['name'],
                                        'feature_category_description': p_feat['description'],
                                        'features': p_feat['features'],
                                        'other_attributes': other_attributes
                                    })
                model.save()
                self.logger.debug('FeatureCategory ID={}, created={}'.format(id, created))
                self.new[id]=model
                self.FCOUNTERS.update({'Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={} ({}): {}'.format(type(e).__name__, id, p_feat['feature_category_name'], str(e))
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    CiderFeatures.objects.get(pk=id).delete()
                    self.FCOUNTERS.update({'Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, str(e)))
        return(True, '')
            
    def Warehouse_Groups(self, info_json):
        self.cur = {}   # Groups currently in database
        self.new = {}   # New groups in document
        for item in CiderGroups.objects.all():
            self.cur[item.info_groupid] = item
        self.logger.debug('Retrieved from database {}/groups'.format(len(self.cur)))

        for p_grp in info_json['groups']:  # Iterating over groups
            id = p_grp['info_groupid']
            # All the attributes, then remove the ones that have their own field
            other_attributes=p_grp.copy()
            for attrib in self.group_model_fields:
                other_attributes.pop(attrib, None)

            try:
                model, created = CiderGroups.objects.update_or_create(
                                    info_groupid=id,
                                    defaults = {
                                        'group_descriptive_name': p_grp['name'],
                                        'group_description': p_grp['description'],
                                        'group_logo_url': p_grp['group_logo_url'],
                                        'group_types': p_grp['group_types'],
                                        'info_resourceids': p_grp.get('info_resourceids'),
                                        'other_attributes': other_attributes
                                    })
                model.save()
                self.logger.debug('Group ID={}, created={}'.format(id, created))
                self.new[id]=model
                self.GCOUNTERS.update({'Update'})
            except (DataError, IntegrityError) as e:
                msg = '{} saving ID={} ({}): {}'.format(type(e).__name__, id, p_grp['group_descriptive_name'], str(e))
                self.logger.error(msg)
                return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    CiderGroups.objects.filter(info_groupid=id).delete()
                    self.GCOUNTERS.update({'Delete'})
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, str(e)))
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
        # Which should be 'begin' or 'end'
        fixed_current_status = current_status.replace('-', '_')
        key = '{}_{}_date'.format(fixed_current_status, which_date)
        if key not in resource_status_dates or resource_status_dates[key] is None:
            return(None)
        try:
            return(datetime.strptime(resource_status_dates[key], "%Y-%m-%d"))
        except:
            return(None)

    def smart_sleep(self, last_run):
        # This functions sleeps, performs refresh checks, and returns when it's time to refresh
        while True:
            if 12 <= datetime.now(timezone.utc).hour <= 24: # Between 6 AM and 6 PM Central (~12 to 24 UTC)
                current_sleep = self.peak_sleep
            else:
                current_sleep = self.off_sleep
            self.logger.debug('sleep({})'.format(current_sleep))
            sleep(current_sleep)

            # Force a refresh every 12 hours at Noon and Midnight UTC
            now_utc = datetime.now(timezone.utc)
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
            if hasattr(self, 'lasturl'):
                ts_json = self.Retrieve_CiDeR_by_Affiliation(self.lasturl)
            try:
                last_db_update = parse_datetime(ts_json['last_update_time'])
                self.logger.info('Last DB update at {} with last refresh at {}'.format(last_db_update, last_run))
                if last_db_update > last_run:
                    self.logger.info('REFRESH TRIGGER: DB update since last run')
                    return
            except Exception as e:
                self.logger.error('{} parsing last_update_time={}: {}'.format(type(e).__name__, ts_json['last_update_time'], str(e)))
                last_db_update = None

    def Run(self):
        while True:
            loop_start_utc = datetime.now(timezone.utc)
            self.RCOUNTERS = Counter() # Resource
            self.FCOUNTERS = Counter() # Resource
            self.GCOUNTERS = Counter() # Group            self.GCOUNTERS = Counter() # Group

            if self.srcparsed.scheme == 'file':
                RAW = self.Read_Cache(self.srcparsed.path)
            else:
                RAW = self.Retrieve_Infrastructure(self.srcparsed)

            if RAW:
                if self.dest['scheme'] == 'file':
                    bytes = self.Write_Cache(self.dest['path'], RAW)
                elif self.dest['scheme'] == 'analyze':
                    self.Analyze_Info(RAW)
                elif self.dest['scheme'] == 'warehouse':
                    pa_application=os.path.basename(__file__)
                    pa_function='Operations_Router_CiDeR'
                    pa_topic = 'Cyberinfrastructure Description'
                    pa_about = ','.join(self.AFFILIATIONS)
                    pa_id = '{}:{}:{}'.format(pa_application, pa_function, pa_topic)
                    pa = ProcessingActivity(pa_application, pa_function, pa_id , pa_topic, pa_about)
                    (rc, warehouse_msg) = self.Warehouse_Resources(RAW)
                    if hasattr(self, 'featuresurl'):
                        RAWFEATURES = self.Retrieve_CiDeR_by_Affiliation(self.featuresurl)
                        (rc2, warehouse_msg2) = self.Warehouse_Features(RAWFEATURES)
                        if rc2:
                            rc = max(rc, rc2)
                        if warehouse_msg2:
                            if warehouse_msg:
                                warehouse_msg = '; '.join(warehouse_msg, warehouse_msg2)
                            else:
                                warehouse_msg = warehouse_msg2
                    if hasattr(self, 'groupsurl'):
                        RAWGROUPS = self.Retrieve_CiDeR_by_Affiliation(self.groupsurl)
                        (rc3, warehouse_msg3) = self.Warehouse_Groups(RAWGROUPS)
                        if rc3:
                            rc = max(rc, rc3)
                        if warehouse_msg3:
                            if warehouse_msg:
                                warehouse_msg = '; '.join(warehouse_msg, warehouse_msg3)
                            else:
                                warehouse_msg = warehouse_msg3

                loop_end_utc = datetime.now(timezone.utc)
                summary_msg = 'Processed resources in {:.3f}/seconds: {}/updates, {}/deletes, {}/skipped'.format((loop_end_utc - loop_start_utc).total_seconds(), self.RCOUNTERS['Update'], self.RCOUNTERS['Delete'], self.RCOUNTERS['Skip'])
                if hasattr(self, 'featuresurl'):
                    summary_msg = summary_msg + '; {}/feature group updates'.format(self.FCOUNTERS['Update'])
                if hasattr(self, 'groupsurl'):
                    summary_msg = summary_msg + '; {}/group updates'.format(self.GCOUNTERS['Update'])
                self.logger.info(summary_msg)
                if self.dest['scheme'] == 'warehouse':
                    if rc:  # No errors
                        pa.FinishActivity(rc, summary_msg)
                    else:   # Something failed, use returned message
                        pa.FinishActivity(rc, warehouse_msg)
            if self.args.once:
                break
            # Continuous
            self.smart_sleep(loop_start_utc)

########## CUSTOMIZATIONS END ##########

if __name__ == '__main__':
    router = Router()
    with PidFile(router.pidfile_path):
        try:
            router.Setup()
            rc = router.Run()
        except Exception as e:
            msg = '{} Exception: {}'.format(type(e).__name__, e)
            router.logger.error(msg)
            traceback.print_exc(file=sys.stdout)
            rc = 1
    router.exit(rc)
