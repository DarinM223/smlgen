../smlgen --test test7.sml person:c foo:c
if cmp --silent test7.sml.test test7.sml.expected; then
  echo "test7 succeeded"
else
  echo "test7 failed"
  echo "Diff:"
  diff test7.sml.test test7.sml.expected
  exit 1
fi