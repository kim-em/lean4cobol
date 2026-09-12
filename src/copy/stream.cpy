01 stream-state.
   02 stream-handle pic x(4).
   02 stream-offset pic 9(18) comp-x.
   02 stream-size pic 9(18) comp-x.
   02 stream-nbytes pic 9(9) comp-x.
   02 stream-pos binary-long unsigned.
   02 stream-available binary-long unsigned.
   02 stream-eof binary-char unsigned.
   02 stream-opened binary-char unsigned.
   02 stream-buffer pic x(65536).
