*> Request modes: 0 lift loose bvars by tx-amount; 1 instantiate;
*> 2 instantiateRev; 3 abstract (tx-count is the abstractRange prefix);
*> 4 instantiateLevelParams; 5 replace with a named COBOL callback.
*> Vectors contain (key,value) pairs. Modes 1/2/3 use value only;
*> mode 4 uses name keys and level values, first duplicate key wins.
01 transform-state.
   02 tx-mode binary-long unsigned.
   02 tx-count binary-long unsigned.
   02 tx-values usage pointer.
   02 tx-amount binary-long unsigned.
   02 tx-callback pic x(64).
   02 tx-context usage pointer.
   02 tx-cache-ptr usage pointer.
   02 tx-cache-cap binary-long unsigned.
   02 tx-cache-count binary-long unsigned.
   02 tx-work binary-long unsigned.
