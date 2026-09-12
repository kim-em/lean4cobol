01 blob-arena based.
   02 blob-node occurs 1 to unbounded depending on blob-cap.
      03 blob-start binary-long unsigned.
      03 blob-length binary-long unsigned.
      03 blob-hash binary-double unsigned.
01 blob-htable based.
   02 blob-slot binary-long unsigned occurs 1 to unbounded
      depending on blob-hcap.
