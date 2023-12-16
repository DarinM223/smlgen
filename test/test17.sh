../smlgen --test test17.sml t:s test17.sig FOO.t:s test17.fun Foo.t:s test17 t:s
if cmp --silent test17.sml.test test17.sml.expected && cmp --silent test17.sig.test test17.sig.expected && cmp --silent test17.fun.test test17.fun.expected && cmp --silent test17.test test17.expected; then
  echo "test17 succeeded"
else
  echo "test17 failed"
  echo "Diff:"
  diff test17.sml.test test17.sml.expected
  diff test17.sig.test test17.sig.expected
  diff test17.fun.test test17.fun.expected
  diff test17.test test17.expected
  exit 1
fi