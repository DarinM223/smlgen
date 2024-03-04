../smlgen test20.sml no:s --recurmod --test
if cmp --silent test20.sml.test test20.sml.expected; then
  echo "test20 succeeded"
else
  echo "test20 failed"
  echo "Diff:"
  diff test20.sml.test test20.sml.expected
  exit 1
fi