cp test5.sml test9.sml
../smlgen --test test9.sml stmt:c foo:c hello:c
if cmp --silent test9.sml.test test9.sml.expected; then
  echo "test9 succeeded"
else
  echo "test9 failed"
  echo "Diff:"
  diff test9.sml.test test9.sml.expected
  exit 1
fi