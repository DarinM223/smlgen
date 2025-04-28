../smlgen --test test15.sml t:gsce result:gsce
if cmp --silent test15.sml.test test15.sml.expected; then
  echo "test15 succeeded"
else
  echo "test15 failed"
  echo "Diff:"
  diff test15.sml.test test15.sml.expected
  exit 1
fi