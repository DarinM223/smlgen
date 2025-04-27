../smlgen --test test24.sml foo:sce bar:sc ref_test:ce
if cmp --silent test24.sml.test test24.sml.expected; then
  echo "test24 succeeded"
else
  echo "test24 failed"
  echo "Diff:"
  diff test24.sml.test test24.sml.expected
  exit 1
fi