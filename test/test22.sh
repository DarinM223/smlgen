../smlgen test22.sml no:s --recurmod --test
if cmp --silent test22.sml.test test22.sml.expected; then
  echo "test22 succeeded"
else
  echo "test22 failed"
  echo "Diff:"
  diff test22.sml.test test22.sml.expected
  exit 1
fi