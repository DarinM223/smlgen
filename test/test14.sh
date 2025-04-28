../smlgen --test test14.sml Lam.varname:gsce Lam.exp:gsce Typ.qname:gsce Typ.tv:gsce
if cmp --silent test14.sml.test test14.sml.expected; then
  echo "test14 succeeded"
else
  echo "test14 failed"
  echo "Diff:"
  diff test14.sml.test test14.sml.expected
  exit 1
fi