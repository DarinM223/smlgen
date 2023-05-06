cd test
succeeded=0
failed=0
for filename in *.sh; do
  if sh $filename; then
    succeeded=$((succeeded+1))
  else
    failed=$((failed+1))
  fi
done

echo Succeeded: $succeeded Failed: $failed