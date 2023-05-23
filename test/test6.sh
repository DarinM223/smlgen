../smlgen --test test6.sml Foo.t:s Bar.t:s
if cmp --silent test6.sml.test test6.sml.expected; then
  echo "test6 succeeded"
else
  echo "test6 failed"
  echo "Diff:"
  diff test6.sml.test test6.sml.expected
  exit 1
fi