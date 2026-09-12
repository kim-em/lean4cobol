*> h := (48271*h + input) mod (2^31-1). Schrage decomposition:
*> 2^31-1 = 48271*44488 + 3399. Each product fits signed 32 bits.
*> Hash collisions only select candidates; full keys are always compared.
hash-mix.
    move hash-acc to hash-quot
    divide 44488 into hash-quot
    move hash-quot to hash-rem
    multiply 44488 by hash-rem
    subtract hash-rem from hash-acc
    multiply 48271 by hash-acc
    multiply 3399 by hash-quot
    subtract hash-quot from hash-acc
    if hash-acc < 0 add 2147483647 to hash-acc end-if
    evaluate true
      when hash-input >= 4294967294
        subtract 4294967294 from hash-input giving hash-digit
      when hash-input >= 2147483647
        subtract 2147483647 from hash-input giving hash-digit
      when other move hash-input to hash-digit
    end-evaluate
    move 214748364 to hash-room
    multiply 10 by hash-room
    add 7 to hash-room
    subtract hash-digit from hash-room
    if hash-acc >= hash-room
        subtract hash-room from hash-acc
    else
        add hash-digit to hash-acc
    end-if.
