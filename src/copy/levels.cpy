*> Kinds: 0 zero, 1 succ, 2 max, 3 imax, 4 parameter.
01 level-arena based.
   02 level-node occurs 1 to unbounded
      depending on level-cap.
      03 level-kind binary-long unsigned.
      03 level-a binary-long unsigned.
      03 level-b binary-long unsigned.
      03 level-has-param binary-char unsigned.
      03 level-never-zero binary-char unsigned.
      03 level-always-zero binary-char unsigned.
      03 level-native-normal binary-long unsigned.
      03 level-offset binary-long unsigned.
      03 level-base binary-long unsigned.
      03 level-hash binary-double unsigned.
01 level-htable based.
   02 level-slot binary-long unsigned occurs 1 to unbounded
      depending on level-hcap.
