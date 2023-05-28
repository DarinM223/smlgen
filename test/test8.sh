../smlgen --test test8.sml person:c foo:c bar:c
if cmp --silent test8.sml.test test8.sml.expected; then
  echo "test8 succeeded"
else
  echo "test8 failed"
  echo "Diff:"
  diff test8.sml.test test8.sml.expected
  exit 1
fi