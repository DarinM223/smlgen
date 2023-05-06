../smlgen --test test1.sml person:g Bop.t:g Anf.value:g Anf.t:g stmt:g
if cmp --silent test1.sml.test test1.sml.expected; then
  echo "test1 succeeded"
else
  echo "test1 failed"
  echo "Diff:"
  diff test1.sml.test test1.sml.expected
  exit 1
fi