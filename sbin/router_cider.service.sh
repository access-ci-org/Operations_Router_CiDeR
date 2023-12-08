#!/bin/bash
do_start () {
    echo -n "Starting %APP_NAME%:"
    export LD_LIBRARY_PATH=${PYTHON_BASE}/lib
    source ${PIPENV_BASE}/bin/activate
    exec ${PYTHON_BIN} ${APP_BIN} --daemon $@ ${APP_OPTS}
    RETVAL=$?
}
do_debug () {
    echo -n "Debugging: ${PIPENV_BASE}/bin/python ${APP_BIN} -l debug $@ ${APP_OPTS}"
    export LD_LIBRARY_PATH=${PYTHON_BASE}/lib
    source ${PIPENV_BASE}/bin/activate
    exec ${PYTHON_BIN} ${APP_BIN} -l debug $@ ${APP_OPTS}
    RETVAL=$?
}

case "$1" in
    start)
        do_start ${@:2}
        ;;

    debug)
        do_debug ${@:2}
        ;;

    *)
        echo "Usage: $0 {start|debug}"
        exit 1
        ;;

esac
echo rc=$RETVAL
exit $RETVAL
