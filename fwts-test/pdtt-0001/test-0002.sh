#!/bin/bash
#
TEST="Test acpitables against invalid PDTT"
NAME=test-0001.sh
TMPLOG=$TMP/pdtt.log.$$

$FWTS --show-tests | grep pdtt > /dev/null
if [ $? -eq 1 ]; then
	echo SKIP: $TEST, $NAME
	exit 77
fi

$FWTS --log-format="%line %owner " -w 80 --dumpfile=$FWTSTESTDIR/pdtt-0001/acpidump-0002.log pdtt - | cut -c7- | grep "^pdtt" > $TMPLOG
diff $TMPLOG $FWTSTESTDIR/pdtt-0001/pdtt-0002.log >> $FAILURE_LOG
ret=$?
if [ $ret -eq 0 ]; then
	echo PASSED: $TEST, $NAME
else
	echo FAILED: $TEST, $NAME
fi

rm $TMPLOG
exit $ret
