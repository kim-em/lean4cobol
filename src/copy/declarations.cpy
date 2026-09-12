*> kind 0 axiom, 1 definition, 2 theorem, 3 opaque,
*> 4 inductive, 5 constructor, 6 recursor, 7 quotient.
*> status 0 unvisited, 1 checking, 2 checked, 3 skipped.
01 decl-arena based.
   02 decl-node occurs 1 to unbounded depending on decl-cap.
      03 decl-name binary-long unsigned.
      03 decl-kind binary-long unsigned.
      03 decl-params binary-long unsigned.
      03 decl-all binary-long unsigned.
      03 decl-hints binary-long unsigned.
      03 decl-height binary-long unsigned.
      03 decl-type binary-long unsigned.
      03 decl-value binary-long unsigned.
      03 decl-unsafe binary-char unsigned.
      03 decl-status binary-char unsigned.
      03 decl-replay binary-char unsigned.
      03 decl-num-params binary-long unsigned.
      03 decl-num-indices binary-long unsigned.
      03 decl-num-fields binary-long unsigned.
      03 decl-num-motives binary-long unsigned.
      03 decl-num-minors binary-long unsigned.
      03 decl-num-nested binary-long unsigned.
      03 decl-ctors binary-long unsigned.
      03 decl-induct binary-long unsigned.
      03 decl-cidx binary-long unsigned.
      03 decl-rules binary-long unsigned.
      03 decl-is-rec binary-char unsigned.
      03 decl-reflexive binary-char unsigned.
      03 decl-k binary-char unsigned.
      03 decl-quot-kind binary-long unsigned.
      03 decl-gen-fields binary-long unsigned.
      03 decl-gen-recargs binary-long unsigned.
      03 decl-gen-result binary-long unsigned.
01 local-arena based.
   02 local-node occurs 1 to unbounded depending on local-cap.
      03 local-type binary-long unsigned.
      03 local-value binary-long unsigned.
01 rule-arena based.
   02 rule-node occurs 1 to unbounded depending on rule-cap.
      03 rule-ctor binary-long unsigned.
      03 rule-fields binary-long unsigned.
      03 rule-rhs binary-long unsigned.
