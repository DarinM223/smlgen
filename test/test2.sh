../smlgen --test test2.sml stmt:g t:g
if cmp --silent test2.sml.test test2.sml.expected; then
  echo "test2 succeeded"
else
  echo "test2 failed"
  echo "Diff:"
  diff test2.sml.test test2.sml.expected
  exit 1
fi