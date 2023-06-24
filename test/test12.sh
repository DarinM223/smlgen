../smlgen --test test12.sml stmt:gsc
if cmp --silent test12.sml.test test12.sml.expected; then
  echo "test12 succeeded"
else
  echo "test12 failed"
  echo "Diff:"
  diff test12.sml.test test12.sml.expected
  exit 1
fi