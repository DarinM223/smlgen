../smlgen --test test11.sml t:gsc
if cmp --silent test11.sml.test test11.sml.expected; then
  echo "test11 succeeded"
else
  echo "test11 failed"
  echo "Diff:"
  diff test11.sml.test test11.sml.expected
  exit 1
fi