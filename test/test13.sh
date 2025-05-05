../smlgen --test test13.sml t:sceh
if cmp --silent test13.sml.test test13.sml.expected; then
  echo "test13 succeeded"
else
  echo "test13 failed"
  echo "Diff:"
  diff test13.sml.test test13.sml.expected
  exit 1
fi