structure RecMod: RECURSIVE_MODULES =
struct
  (*
  1. Track structure levels in environment.
     First pass: For every datatype, make a map from full name (including structures) to the datatype.
     Second pass: Track the current environment of structure name to datatype as well as the current
     structure level. If there is a link to the global environment and the current environment it should
     prefer the current environment.
  2. For every datatype, add links to other datatypes and also store the datatype constructors and types.
  3. Calculate the SCCs of the datatypes to find the connected datatype components.
  4. For each component, generate a merged structure name at the beginning and merge the datatypes
     into a single mutually recursive datatype.
  5. Rewrite the original structures to unpack the corresponding type in the recursive datatype.

  TODO: handle type aliases
  *)
  fun gen _ = raise Fail "Gen not implemented"
end
