#!/bin/bash
#
TEST="Test --results-output stdout option"
NAME=test-0003.sh
TMPLOG=$TMP/results_$$.log

($FWTS --log-format="%line %owner " -w 80 -j $FWTSTESTDIR/../data --klog=$FWTSTESTDIR/arg-results-0001/klog.txt klog --results-output=stdout | grep "^[0-9]*[ ]*klog" | cut -c7- > $TMPLOG ) >& /dev/null
diff $TMPLOG $FWTSTESTDIR/arg-results-0001/results.log >> $FAILURE_LOG
ret=$?
if [ $ret -eq 0 ]; then 
	echo PASSED: $TEST, $NAME
else
	echo FAILED: $TEST, $NAME
fi

rm $TMPLOG
exit $ret
