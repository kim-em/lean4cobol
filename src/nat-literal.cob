*> Literal typing and Nat constructor views. Decimal predecessor uses the
*> canonical arbitrary-length literal bytes; arithmetic is in bignum.cob.
identification division.
program-id. infer-literal.
data division.
local-storage section.
01 k binary-long unsigned.
01 name-id binary-long unsigned.
01 zero-val binary-long unsigned.
01 const-kind binary-long unsigned value 2.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'names.cpy'.
01 input-expr binary-long unsigned.
01 result-type binary-long unsigned.
procedure division using kernel-state input-expr result-type.
    move 0 to result-type
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr move expr-kind(input-expr) to k
    if k = 8
        call 'builtin-name' using kernel-state 'Nat' name-id
        if tc-infer-only = 0
            set address of name-arena to name-ptr
            if name-env(name-id) = 0 move 1 to verdict goback end-if
        end-if
    else
        if tc-infer-only = 0
            call 'builtin-name' using kernel-state 'Char.ofNat' name-id
            set address of name-arena to name-ptr
            if name-env(name-id) = 0 move 1 to verdict goback end-if
            call 'builtin-name' using kernel-state 'String.ofList' name-id
            set address of name-arena to name-ptr
            if name-env(name-id) = 0 move 1 to verdict goback end-if
        end-if
        call 'builtin-name' using kernel-state 'String' name-id
    end-if
    call 'expr-intern' using kernel-state const-kind name-id zero-val zero-val zero-val result-type
    goback.
end program infer-literal.

identification division.
program-id. nat-view.
data division.
local-storage section.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 name-id binary-long unsigned.
01 literal-id binary-long unsigned.
01 start-pos binary-long unsigned.
01 text-size binary-long unsigned.
01 i binary-long unsigned.
01 new-blob binary-long unsigned.
01 buffer-ptr usage pointer.
01 buffer-cap binary-long unsigned.
01 width binary-long unsigned value 1.
01 zero-val binary-long unsigned.
01 nat-kind binary-long unsigned value 8.
01 matched binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'blob.cpy'.
01 string-bytes based.
   02 string-byte pic x occurs 1 to 2000000000 depending on byte-cap.
01 scratch-data based.
   02 scratch-byte pic x occurs 1 to 2000000000 depending on buffer-cap.
01 input-expr binary-long unsigned.
01 is-zero binary-char unsigned.
01 predecessor binary-long unsigned.
procedure division using kernel-state input-expr is-zero predecessor.
    move 0 to is-zero predecessor
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    move expr-kind(input-expr) to k move expr-a(input-expr) to a move expr-b(input-expr) to b
    evaluate k
      when 2
        call 'name-matches' using kernel-state a 'Nat.zero' is-zero
      when 3
        if expr-kind(a) = 2
            move expr-a(a) to name-id
            call 'name-matches' using kernel-state name-id 'Nat.succ' matched
            if matched = 1 move b to predecessor end-if
        end-if
      when 8
        set address of blob-arena to blob-ptr
        move blob-start(a) to start-pos move blob-length(a) to text-size
        set address of string-bytes to byte-ptr
        if text-size = 1 and string-byte(start-pos) = '0' move 1 to is-zero goback end-if
        call 'arena-reserve' using buffer-ptr buffer-cap text-size width verdict
        if verdict not = 0 goback end-if
        set address of scratch-data to buffer-ptr
        move string-bytes(start-pos:text-size) to scratch-data(1:text-size)
        move text-size to i
        perform until i = 0
            if scratch-byte(i) not = '0'
                move function char(function ord(scratch-byte(i)) - 1) to scratch-byte(i)
                exit perform
            end-if
            move '9' to scratch-byte(i) subtract 1 from i
        end-perform
        move 1 to start-pos
        if text-size > 1 and scratch-byte(1) = '0'
            move 2 to start-pos subtract 1 from text-size
        end-if
        call 'blob-intern' using kernel-state scratch-data(start-pos:text-size) text-size new-blob
        call 'expr-intern' using kernel-state nat-kind new-blob zero-val zero-val zero-val predecessor
        call 'arena-release' using buffer-ptr
    end-evaluate
    goback.
end program nat-view.

identification division.
program-id. def-nat-offset recursive.
data division.
local-storage section.
01 lzero binary-char unsigned.
01 rzero binary-char unsigned.
01 lpred binary-long unsigned.
01 rpred binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 depth-val binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs depth-val answer.
    move 2 to answer
    call 'nat-view' using kernel-state lhs lzero lpred
    call 'nat-view' using kernel-state rhs rzero rpred
    if verdict not = 0 goback end-if
    if lzero = 1 and rzero = 1 move 1 to answer goback end-if
    if lpred not = 0 and rpred not = 0
        call 'def-equal-core' using kernel-state lpred rpred depth-val answer
    end-if
    goback.
end program def-nat-offset.

identification division.
program-id. nat-constructor.
data division.
local-storage section.
01 is-zero binary-char unsigned.
01 predecessor binary-long unsigned.
01 name-id binary-long unsigned.
01 fn binary-long unsigned.
01 zero-val binary-long unsigned.
01 const-kind binary-long unsigned value 2.
01 app-kind binary-long unsigned value 3.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr result-expr.
    move input-expr to result-expr
    call 'nat-view' using kernel-state input-expr is-zero predecessor
    if verdict not = 0 goback end-if
    if is-zero = 1
        call 'builtin-name' using kernel-state 'Nat.zero' name-id
        call 'expr-intern' using kernel-state const-kind name-id zero-val zero-val zero-val result-expr
    else
        if predecessor not = 0
            call 'builtin-name' using kernel-state 'Nat.succ' name-id
            call 'expr-intern' using kernel-state const-kind name-id zero-val zero-val zero-val fn
            call 'expr-intern' using kernel-state app-kind fn predecessor zero-val zero-val result-expr
        end-if
    end-if
    goback.
end program nat-constructor.
