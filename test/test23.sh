../smlgen test23.sml no:s --recurmod --test
if cmp --silent test23.sml.test test23.sml.expected; then
  echo "test23 succeeded"
else
  echo "test23 failed"
  echo "Diff:"
  diff test23.sml.test test23.sml.expected
  exit 1
fi