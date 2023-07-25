../smlgen --test test16.sml t:gsc
if cmp --silent test16.sml.test test16.sml.expected; then
  echo "test16 succeeded"
else
  echo "test16 failed"
  echo "Diff:"
  diff test16.sml.test test16.sml.expected
  exit 1
fi