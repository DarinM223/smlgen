../smlgen --test test3.sml stmt:g
if cmp --silent test3.sml.test test3.sml.expected; then
  echo "test3 succeeded"
else
  echo "test3 failed"
  echo "Diff:"
  diff test3.sml.test test3.sml.expected
  exit 1
fi