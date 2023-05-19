../smlgen --test test5.sml stmt:s foo:s
if cmp --silent test5.sml.test test5.sml.expected; then
  echo "test5 succeeded"
else
  echo "test5 failed"
  echo "Diff:"
  diff test5.sml.test test5.sml.expected
  exit 1
fi