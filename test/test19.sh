../smlgen test19.sml no:s --recurmod --test
if cmp --silent test19.sml.test test19.sml.expected; then
  echo "test19 succeeded"
else
  echo "test19 failed"
  echo "Diff:"
  diff test19.sml.test test19.sml.expected
  exit 1
fi