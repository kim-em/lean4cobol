01 name-arena based.
   02 name-node occurs 1 to unbounded
      depending on name-cap.
      03 name-kind binary-long unsigned.
      03 name-pre binary-long unsigned.
      03 name-number binary-double unsigned.
      03 name-start binary-long unsigned.
      03 name-length binary-long unsigned.
      03 name-decl binary-long unsigned.
      03 name-env binary-long unsigned.
      03 name-hash binary-double unsigned.
01 name-htable based.
   02 name-slot binary-long unsigned occurs 1 to unbounded
      depending on name-hcap.
01 string-bytes based.
   02 string-byte pic x occurs 1 to unbounded
      depending on byte-cap.
