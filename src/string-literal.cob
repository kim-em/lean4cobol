*> Lean4Lean.Expr.strLitToConstructor: UTF-8 scalar values become an explicit
*> List.{0} Char under String.ofList. The parser has validated the UTF-8 bytes.
identification division.
program-id. string-constructor.
data division.
local-storage section.
01 blob-id binary-long unsigned.
01 start-pos binary-long unsigned.
01 cursor-pos binary-long unsigned.
01 lead-pos binary-long unsigned.
01 i binary-long unsigned.
01 octet binary-long unsigned.
01 scalar binary-long unsigned.
01 n binary-long unsigned.
01 char-type binary-long unsigned.
01 char-of-nat binary-long unsigned.
01 string-of-list binary-long unsigned.
01 cons-fn binary-long unsigned.
01 tail-id binary-long unsigned.
01 fn binary-long unsigned.
01 char-id binary-long unsigned.
01 literal-id binary-long unsigned.
01 tmp binary-long unsigned.
01 zero-levels binary-long unsigned.
01 zero-val binary-long unsigned.
01 one-val binary-long unsigned value 1.
01 const-kind binary-long unsigned value 2.
01 app-kind binary-long unsigned value 3.
01 nat-kind binary-long unsigned value 8.
01 printed-scalar pic Z(6)9.
01 scalar-text pic x(7).
01 text-size binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'blob.cpy'.
01 string-bytes based.
   02 string-byte pic x occurs 1 to 2000000000 depending on byte-cap.
01 input-expr binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr result-expr.
    move input-expr to result-expr
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(input-expr) not = 9 goback end-if
    move expr-a(input-expr) to blob-id
    set address of blob-arena to blob-ptr
    move blob-start(blob-id) to start-pos
    compute cursor-pos = start-pos + blob-length(blob-id)
    call 'builtin-name' using kernel-state 'Char' n
    call 'expr-intern' using kernel-state const-kind n zero-val zero-val zero-val char-type
    call 'builtin-name' using kernel-state 'Char.ofNat' n
    call 'expr-intern' using kernel-state const-kind n zero-val zero-val zero-val char-of-nat
    call 'builtin-name' using kernel-state 'String.ofList' n
    call 'expr-intern' using kernel-state const-kind n zero-val zero-val zero-val string-of-list
    call 'list-intern' using kernel-state one-val zero-val zero-levels
    call 'builtin-name' using kernel-state 'List.nil' n
    call 'expr-intern' using kernel-state const-kind n zero-levels zero-val zero-val fn
    call 'expr-intern' using kernel-state app-kind fn char-type zero-val zero-val tail-id
    call 'builtin-name' using kernel-state 'List.cons' n
    call 'expr-intern' using kernel-state const-kind n zero-levels zero-val zero-val fn
    call 'expr-intern' using kernel-state app-kind fn char-type zero-val zero-val cons-fn
    perform until cursor-pos <= start-pos or verdict not = 0
        subtract 1 from cursor-pos
        move cursor-pos to lead-pos
        set address of string-bytes to byte-ptr
        compute octet = function ord(string-byte(lead-pos)) - 1
        perform until octet < 128 or octet >= 192
            subtract 1 from lead-pos
            compute octet = function ord(string-byte(lead-pos)) - 1
        end-perform
        evaluate true
          when octet < 128 move octet to scalar
          when octet < 224 compute scalar = octet - 192
          when octet < 240 compute scalar = octet - 224
          when other compute scalar = octet - 240
        end-evaluate
        move lead-pos to i
        add 1 to i
        perform until i > cursor-pos
            compute scalar = scalar * 64 + function ord(string-byte(i)) - 129
            add 1 to i
        end-perform
        move lead-pos to cursor-pos
        move scalar to printed-scalar
        move function trim(printed-scalar) to scalar-text
        compute text-size = function length(function trim(printed-scalar))
        call 'blob-intern' using kernel-state scalar-text text-size blob-id
        call 'expr-intern' using kernel-state nat-kind blob-id zero-val zero-val zero-val literal-id
        call 'expr-intern' using kernel-state app-kind char-of-nat literal-id zero-val zero-val char-id
        call 'expr-intern' using kernel-state app-kind cons-fn char-id zero-val zero-val fn
        call 'expr-intern' using kernel-state app-kind fn tail-id zero-val zero-val tmp
        move tmp to tail-id
    end-perform
    call 'expr-intern' using kernel-state app-kind string-of-list tail-id zero-val zero-val result-expr
    goback.
end program string-constructor.

identification division.
program-id. def-string-core recursive.
data division.
local-storage section.
01 fn binary-long unsigned.
01 n binary-long unsigned.
01 expanded binary-long unsigned.
01 next-depth binary-long unsigned.
01 matched binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 depth-val binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs depth-val answer.
    move 2 to answer
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(lhs) not = 9 or expr-kind(rhs) not = 3 goback end-if
    move expr-a(rhs) to fn
    if expr-kind(fn) not = 2 or expr-b(fn) not = 0 goback end-if
    move expr-a(fn) to n
    call 'name-matches' using kernel-state n 'String.ofList' matched
    if matched = 0 goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    call 'string-constructor' using kernel-state lhs expanded
    call 'def-equal-core' using kernel-state expanded rhs next-depth answer
    goback.
end program def-string-core.
