../smlgen --test test25.sml t:sceh Module.hello:sceh -maxexpdepth 10
if cmp --silent test25.sml.test test25.sml.expected; then
  echo "test25 succeeded"
else
  echo "test25 failed"
  echo "Diff:"
  diff test25.sml.test test25.sml.expected
  exit 1
fi