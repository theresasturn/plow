
$XSB -e "[testall],testall,halt." >& /dev/null

status=0
diff -w plowtest_new plowtest_old || status=1
if test "$status" = 0; then
   echo "plow successfully tested"
   rm -r plowtest_new
else
   echo "!!!plow failed :-("
   diff -w plowtest_new plowtest_old
fi
