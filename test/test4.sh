../smlgen --test test4.sml person:u t:u
if cmp --silent test4.sml.test test4.sml.expected; then
  echo "test4 succeeded"
else
  echo "test4 failed"
  echo "Diff:"
  diff test4.sml.test test4.sml.expected
  exit 1
fi