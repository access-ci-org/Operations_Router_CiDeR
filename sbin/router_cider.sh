#!/bin/sh

###
# Run %APP_NAME% interactively
###

APP_NAME=%APP_NAME%
APP_HOME=%APP_HOME%
WAREHOUSE_DJANGO=%WAREHOUSE_DJANGO%
# Override in shell environment
if [ -z "$PYTHON_BASE" ]; then
    PYTHON_BASE=%PYTHON_BASE%
fi

####### Everything else should be standard #######
APP_SOURCE=${APP_HOME}/PROD
APP_BIN=${APP_SOURCE}/bin/${APP_NAME}.py
APP_OPTS="-l info -c ${APP_HOME}/conf/${APP_NAME}.conf"

PYTHON_BIN=python3
export LD_LIBRARY_PATH=${PYTHON_BASE}/lib
source ${APP_HOME}/python/bin/activate

export PYTHONPATH=${APP_SOURCE}/lib:${WAREHOUSE_DJANGO}
export APP_CONFIG=${APP_HOME}/conf/django_prod_router.conf
export DJANGO_SETTINGS_MODULE=Operations_Warehouse_Django.settings

echo "Starting: ${PYTHON_BIN} ${APP_BIN} $@ ${APP_OPTS}"
${PYTHON_BIN} ${APP_BIN} $@ ${APP_OPTS}
RETVAL=$?
echo rc=$RETVAL
exit $RETVAL
