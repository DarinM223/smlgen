cp test6.sml test10.sml
../smlgen --test test10.sml Foo.t:c Foo.foo:c Bar.t:c Bar.bar:c
if cmp --silent test10.sml.test test10.sml.expected; then
  echo "test10 succeeded"
else
  echo "test10 failed"
  echo "Diff:"
  diff test10.sml.test test10.sml.expected
  exit 1
fi