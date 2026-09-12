*> TypeChecker.reduceNative rejects the two unsupported host-code hooks.
identification division.
program-id. reduce-native.
data division.
local-storage section.
01 fn binary-long unsigned.
01 arg-id binary-long unsigned.
01 n binary-long unsigned.
01 matched binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
procedure division using kernel-state input-expr.
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(input-expr) not = 3 goback end-if
    move expr-a(input-expr) to fn move expr-b(input-expr) to arg-id
    if expr-kind(fn) not = 2 or expr-kind(arg-id) not = 2 goback end-if
    if expr-b(fn) not = 0 goback end-if
    move expr-a(fn) to n
    call 'name-matches' using kernel-state n 'Lean.reduceBool' matched
    if matched = 1 move 1 to verdict goback end-if
    call 'name-matches' using kernel-state n 'Lean.reduceNat' matched
    if matched = 1 move 1 to verdict end-if
    goback.
end program reduce-native.

*> rawNatLitExt?: a literal or the exact constant Nat.zero.{}, not a
*> successor expression or a zero constant with extra universe arguments.
identification division.
program-id. nat-raw-blob.
data division.
local-storage section.
01 n binary-long unsigned.
01 matched binary-char unsigned.
01 one-val binary-long unsigned value 1.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
01 result-blob binary-long unsigned.
procedure division using kernel-state input-expr result-blob.
    move 0 to result-blob
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(input-expr) = 8
        move expr-a(input-expr) to result-blob goback
    end-if
    if expr-kind(input-expr) not = 2 or expr-b(input-expr) not = 0 goback end-if
    move expr-a(input-expr) to n
    call 'name-matches' using kernel-state n 'Nat.zero' matched
    if matched = 1 call 'blob-intern' using kernel-state '0' one-val result-blob end-if
    goback.
end program nat-raw-blob.

identification division.
program-id. reduce-nat recursive.
data division.
working-storage section.
01 spellings.
   02 filler pic x(16) value 'Nat.add'.
   02 filler pic x(16) value 'Nat.sub'.
   02 filler pic x(16) value 'Nat.mul'.
   02 filler pic x(16) value 'Nat.div'.
   02 filler pic x(16) value 'Nat.mod'.
   02 filler pic x(16) value 'Nat.gcd'.
   02 filler pic x(16) value 'Nat.beq'.
   02 filler pic x(16) value 'Nat.ble'.
   02 filler pic x(16) value 'Nat.land'.
   02 filler pic x(16) value 'Nat.lor'.
   02 filler pic x(16) value 'Nat.xor'.
   02 filler pic x(16) value 'Nat.shiftLeft'.
   02 filler pic x(16) value 'Nat.shiftRight'.
   02 filler pic x(16) value 'Nat.pow'.
01 spelling-table redefines spellings.
   02 spelling pic x(16) occurs 14.
local-storage section.
01 fn binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 n binary-long unsigned.
01 unary-op binary-char unsigned.
01 operation binary-long unsigned.
01 left-blob binary-long unsigned.
01 right-blob binary-long unsigned.
01 result-blob binary-long unsigned.
01 reduced binary-long unsigned.
01 next-depth binary-long unsigned.
01 matched binary-char unsigned.
01 zero-val binary-long unsigned.
01 one-val binary-long unsigned value 1.
01 const-kind binary-long unsigned value 2.
01 nat-kind binary-long unsigned value 8.
01 text-size binary-long unsigned.
01 text-start binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'blob.cpy'.
01 string-bytes based.
   02 string-byte pic x occurs 1 to 2000000000 depending on byte-cap.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-expr.
    move 0 to result-expr
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    set address of expr-arena to expr-ptr
    if expr-kind(input-expr) not = 3 goback end-if
    move expr-a(input-expr) to fn move expr-b(input-expr) to b
    evaluate expr-kind(fn)
      when 2
        if expr-b(fn) not = 0 goback end-if
        move expr-a(fn) to n
        call 'name-matches' using kernel-state n 'Nat.succ' matched
        if matched = 0 goback end-if
        move b to a move 1 to unary-op operation
      when 3
        move expr-b(fn) to a move expr-a(fn) to fn
        if expr-kind(fn) not = 2 goback end-if
        move expr-a(fn) to n
        perform varying operation from 1 by 1 until operation > 14
            call 'name-matches' using kernel-state n spelling(operation) matched
            if matched = 1 exit perform end-if
        end-perform
        if operation > 14 goback end-if
      when other goback
    end-evaluate
    call 'weak-head' using kernel-state a next-depth reduced
    call 'nat-raw-blob' using kernel-state reduced left-blob
    if left-blob = 0 or verdict not = 0 goback end-if
    if unary-op = 1
        call 'blob-intern' using kernel-state '1' one-val right-blob
    else
        call 'weak-head' using kernel-state b next-depth reduced
        call 'nat-raw-blob' using kernel-state reduced right-blob
        if right-blob = 0 or verdict not = 0 goback end-if
    end-if
    if operation = 14
        set address of blob-arena to blob-ptr
        move blob-length(right-blob) to text-size move blob-start(right-blob) to text-start
        if text-size > 8 goback end-if
        set address of string-bytes to byte-ptr
        if function numval(string-bytes(text-start:text-size)) > 16777216 goback end-if
    end-if
    call 'bignum-calc' using kernel-state operation left-blob right-blob result-blob
    if verdict not = 0 goback end-if
    if operation = 7 or 8
        set address of blob-arena to blob-ptr
        set address of string-bytes to byte-ptr
        if string-byte(blob-start(result-blob)) = '1'
            call 'builtin-name' using kernel-state 'Bool.true' n
        else call 'builtin-name' using kernel-state 'Bool.false' n end-if
        call 'expr-intern' using kernel-state const-kind n zero-val zero-val zero-val result-expr
    else
        call 'expr-intern' using kernel-state nat-kind result-blob zero-val zero-val zero-val result-expr
    end-if
    goback.
end program reduce-nat.
