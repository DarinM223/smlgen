../smlgen test21.sml no:s --recurmod --test
if cmp --silent test21.sml.test test21.sml.expected; then
  echo "test21 succeeded"
else
  echo "test21 failed"
  echo "Diff:"
  diff test21.sml.test test21.sml.expected
  exit 1
fi