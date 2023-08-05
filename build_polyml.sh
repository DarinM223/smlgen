mlton -stop f smlgen.mlb | grep -v ".mlb" | while read line ; do echo "use \"$line\";" ; done > build.sml
