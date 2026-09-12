*> 0 bvar, 1 sort, 2 const, 3 app, 4 lam, 5 forall, 6 let,
*> 7 proj, 8 nat literal, 9 string literal, 10 fvar, 11 mdata.
*> Binder names/info are ignored by eqv; let nondep is significant.
01 expr-arena based.
   02 expr-node occurs 1 to unbounded depending on expr-cap.
      03 expr-replay-stamp binary-long unsigned.
      03 expr-kind binary-long unsigned.
      03 expr-a binary-long unsigned.
      03 expr-b binary-long unsigned.
      03 expr-c binary-long unsigned.
      03 expr-d binary-long unsigned.
      03 expr-hash binary-double unsigned.
      03 expr-lbvr binary-long unsigned.
      03 expr-has-fvar binary-char unsigned.
      03 expr-has-param binary-char unsigned.
      03 expr-has-string binary-char unsigned.
01 expr-htable based.
   02 expr-slot binary-long unsigned occurs 1 to unbounded
      depending on expr-hcap.
