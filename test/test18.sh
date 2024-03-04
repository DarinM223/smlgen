../smlgen test18.sml no:s --recurmod --test
if cmp --silent test18.sml.test test18.sml.expected; then
  echo "test18 succeeded"
else
  echo "test18 failed"
  echo "Diff:"
  diff test18.sml.test test18.sml.expected
  exit 1
fi