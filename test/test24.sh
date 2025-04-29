../smlgen --test test24.sml Foo.t:sce Bar.t:sce Bar.bar:sce
if cmp --silent test24.sml.test test24.sml.expected; then
  echo "test24 succeeded"
else
  echo "test24 failed"
  echo "Diff:"
  diff test24.sml.test test24.sml.expected
  exit 1
fi