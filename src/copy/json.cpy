01 json-state.
   02 json-input pic x(4000001).
   02 json-length binary-long unsigned.
   02 json-pos binary-long unsigned.
   02 json-decoded pic x(4000001).
   02 json-used binary-long unsigned.
   02 json-count binary-long unsigned.
   02 json-cap binary-long unsigned.
   02 json-ptr usage pointer.
   02 scan-status binary-long signed.
01 json-arena based.
   02 json-token occurs 1 to 4194304 depending on json-cap.
      03 json-kind pic x.
      03 json-start binary-long unsigned.
      03 json-size binary-long unsigned.
      03 json-next binary-long unsigned.
