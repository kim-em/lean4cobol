*> Interned handle lists: 0 is nil; each cell has a head and tail.
01 list-arena based.
   02 list-node occurs 1 to unbounded depending on list-cap.
      03 list-a binary-long unsigned.
      03 list-b binary-long unsigned.
      03 list-hash binary-double unsigned.
      03 list-length binary-long unsigned.
01 list-htable based.
   02 list-slot binary-long unsigned occurs 1 to unbounded
      depending on list-hcap.
