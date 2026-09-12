*> Binder-aware Expr operations, ported from Lean.Expr/Lean.Util.ReplaceExpr.
*> Copyright (c) Microsoft Corporation; COBOL port under Apache-2.0.
identification division.
program-id. expr-ops recursive.
data division.
local-storage section.
01 zero-depth binary-long unsigned.
01 stable-input binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'transform.cpy'.
01 input-expr binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state transform-state input-expr result-expr.
    move input-expr to result-expr
    if verdict not = 0 goback end-if
    if tx-mode >= 1 and tx-mode <= 4 and tx-count = 0 goback end-if
    move 0 to tx-cache-cap tx-cache-count
    set tx-cache-ptr to null
    move 1000000 to tx-work
    move input-expr to stable-input
    call 'expr-walk' using kernel-state transform-state stable-input
        zero-depth zero-depth result-expr
    if tx-cache-ptr not = null call 'arena-release' using tx-cache-ptr end-if
    move 0 to tx-cache-cap tx-cache-count
    goback.
end program expr-ops.

identification division.
program-id. expr-walk recursive.
data division.
local-storage section.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 arg-c-val binary-long unsigned.
01 arg-d-val binary-long unsigned.
01 na binary-long unsigned.
01 nb binary-long unsigned.
01 nc binary-long unsigned.
01 i binary-long unsigned.
01 cache-key binary-long unsigned.
01 cached-depth binary-long unsigned.
01 zero-val binary-long unsigned.
01 next-depth binary-long unsigned.
01 next-binding binary-long unsigned.
01 lifted binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'transform.cpy'.
copy 'transform-views.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
01 binding-depth binary-long unsigned.
01 recursion-depth binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state transform-state input-expr
    binding-depth recursion-depth result-expr.
    move input-expr to result-expr
    if verdict not = 0 goback end-if
    if recursion-depth >= recursion-limit or tx-work = 0
        move 2 to verdict goback
    end-if
    subtract 1 from tx-work
    set address of expr-arena to expr-ptr
    if input-expr = 0 or input-expr > expr-count
        move 3 to verdict goback
    end-if
    if tx-mode <= 2 and expr-lbvr(input-expr) <= binding-depth goback end-if
    if tx-mode = 3 and expr-has-fvar(input-expr) = 0 goback end-if
    if tx-mode = 4 and expr-has-param(input-expr) = 0 goback end-if
    compute cache-key = input-expr * 2
    if tx-mode <= 3 move binding-depth to cached-depth end-if
    call 'transform-cache' using kernel-state transform-state cache-key
        cached-depth zero-val result-expr
    if result-expr not = 0 goback end-if
    move input-expr to result-expr
    move expr-kind(input-expr) to k
    move expr-a(input-expr) to a na
    move expr-b(input-expr) to b nb
    move expr-c(input-expr) to arg-c-val nc
    move expr-d(input-expr) to arg-d-val
    if tx-mode = 5
        move 0 to result-expr
        call function trim(tx-callback) using kernel-state tx-context
            input-expr result-expr
        if verdict not = 0 goback end-if
        if result-expr not = 0 perform remember goback end-if
        move input-expr to result-expr
    end-if
    move recursion-depth to next-depth
    add 1 to next-depth
    move binding-depth to next-binding
    add 1 to next-binding
    evaluate true
      when k = 0 and tx-mode <= 2
        if a >= binding-depth
            if tx-mode = 0
                if a > 4294967294 - tx-amount
                    move 2 to verdict goback
                end-if
                move a to na
                add tx-amount to na
            else
                move a to i
                subtract binding-depth from i
                if i < tx-count
                    if tx-mode = 1 add 1 to i else
                        compute i = tx-count - i
                    end-if
                    set address of tx-vector to tx-values
                    move tx-value(i) to lifted
                    if binding-depth > 0
                        call 'expr-lift' using kernel-state lifted
                            binding-depth result-expr
                    else move lifted to result-expr end-if
                    perform remember goback
                else compute na = a - tx-count end-if
            end-if
        end-if
      when k = 10 and tx-mode = 3
        set address of tx-vector to tx-values
        move tx-count to i
        perform until i = 0
            if tx-value(i) = input-expr
                move 0 to k nb nc arg-d-val
                compute na = binding-depth + tx-count - i
                exit perform
            end-if
            subtract 1 from i
        end-perform
      when k = 1 and tx-mode = 4
        call 'level-substitute' using kernel-state transform-state a
            next-depth na
      when k = 2 and tx-mode = 4
        call 'level-list-substitute' using kernel-state transform-state b
            next-depth nb
      when k = 3
        perform walk-a perform walk-b
      when k = 4 or k = 5
        perform walk-a
        call 'expr-walk' using kernel-state transform-state b
            next-binding next-depth nb
      when k = 6
        perform walk-a perform walk-b
        call 'expr-walk' using kernel-state transform-state arg-c-val
            next-binding next-depth nc
      when k = 7
        call 'expr-walk' using kernel-state transform-state arg-c-val
            binding-depth next-depth nc
      when k = 11 perform walk-a
    end-evaluate
    if verdict = 0
        call 'expr-intern' using kernel-state k na nb nc arg-d-val result-expr
    end-if
    perform remember
    goback.
walk-a.
    call 'expr-walk' using kernel-state transform-state a
        binding-depth next-depth na.
walk-b.
    call 'expr-walk' using kernel-state transform-state b
        binding-depth next-depth nb.
remember.
    call 'transform-cache' using kernel-state transform-state cache-key
        cached-depth result-expr lifted.
end program expr-walk.

identification division.
program-id. expr-lift recursive.
data division.
local-storage section.
copy 'transform.cpy'.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 amount-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr amount-val result-expr.
    move 0 to tx-mode
    move amount-val to tx-amount
    call 'expr-ops' using kernel-state transform-state input-expr result-expr
    goback.
end program expr-lift.

identification division.
program-id. expr-instantiate1 recursive.
data division.
local-storage section.
copy 'transform.cpy'.
01 one-substitution.
   02 unused-key binary-long unsigned.
   02 replacement binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 subst-expr binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr subst-expr result-expr.
    move 1 to tx-mode tx-count
    move subst-expr to replacement
    set tx-values to address of one-substitution
    call 'expr-ops' using kernel-state transform-state input-expr result-expr
    goback.
end program expr-instantiate1.

identification division.
program-id. level-substitute recursive.
data division.
local-storage section.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 na binary-long unsigned.
01 nb binary-long unsigned.
01 i binary-long unsigned.
01 next-depth binary-long unsigned.
01 cache-key binary-long unsigned.
01 zero-val binary-long unsigned.
01 ignored-val binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'transform.cpy'.
copy 'transform-views.cpy'.
copy 'levels.cpy'.
01 input-level binary-long unsigned.
01 recursion-depth binary-long unsigned.
01 result-level binary-long unsigned.
procedure division using kernel-state transform-state input-level
    recursion-depth result-level.
    move input-level to result-level
    if verdict not = 0 goback end-if
    if recursion-depth >= recursion-limit or tx-work = 0
        move 2 to verdict goback
    end-if
    subtract 1 from tx-work
    set address of level-arena to level-ptr
    if level-has-param(input-level) = 0 goback end-if
    compute cache-key = input-level * 2 + 1
    call 'transform-cache' using kernel-state transform-state cache-key
        zero-val zero-val result-level
    if result-level not = 0 goback end-if
    move input-level to result-level
    move level-kind(input-level) to k
    move level-a(input-level) to a na
    move level-b(input-level) to b nb
    move recursion-depth to next-depth
    add 1 to next-depth
    if k = 4
        set address of tx-vector to tx-values
        perform varying i from 1 by 1 until i > tx-count
            if tx-key(i) = a
                move tx-value(i) to result-level exit perform
            end-if
        end-perform
    else
        call 'level-substitute' using kernel-state transform-state a
            next-depth na
        if k = 2 or 3
            call 'level-substitute' using kernel-state transform-state b
                next-depth nb
        end-if
        call 'level-make' using kernel-state k na nb result-level
    end-if
    call 'transform-cache' using kernel-state transform-state cache-key
        zero-val result-level ignored-val
    goback.
end program level-substitute.

identification division.
program-id. level-list-substitute recursive.
data division.
local-storage section.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 na binary-long unsigned.
01 nb binary-long unsigned.
01 next-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'transform.cpy'.
copy 'list.cpy'.
01 input-list binary-long unsigned.
01 recursion-depth binary-long unsigned.
01 result-list binary-long unsigned.
procedure division using kernel-state transform-state input-list
    recursion-depth result-list.
    move input-list to result-list
    if verdict not = 0 or input-list = 0 goback end-if
    if recursion-depth >= recursion-limit
        move 2 to verdict goback
    end-if
    move recursion-depth to next-depth
    add 1 to next-depth
    set address of list-arena to list-ptr
    move list-a(input-list) to a
    move list-b(input-list) to b
    call 'level-substitute' using kernel-state transform-state a next-depth na
    call 'level-list-substitute' using kernel-state transform-state b next-depth nb
    call 'list-intern' using kernel-state na nb result-list
    goback.
end program level-list-substitute.

identification division.
program-id. expr-instantiate recursive.
data division.
local-storage section.
copy 'transform.cpy'.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 vector-count binary-long unsigned.
01 vector-ptr usage pointer.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr vector-count vector-ptr result-expr.
    move 1 to tx-mode
    move vector-count to tx-count
    set tx-values to vector-ptr
    call 'expr-ops' using kernel-state transform-state input-expr result-expr
    goback.
end program expr-instantiate.

identification division.
program-id. expr-instantiate-rev recursive.
data division.
local-storage section.
copy 'transform.cpy'.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 vector-count binary-long unsigned.
01 vector-ptr usage pointer.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr vector-count vector-ptr result-expr.
    move 2 to tx-mode
    move vector-count to tx-count
    set tx-values to vector-ptr
    call 'expr-ops' using kernel-state transform-state input-expr result-expr
    goback.
end program expr-instantiate-rev.

identification division.
program-id. expr-abstract recursive.
data division.
local-storage section.
copy 'transform.cpy'.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 vector-count binary-long unsigned.
01 vector-ptr usage pointer.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr vector-count vector-ptr result-expr.
    move 3 to tx-mode
    move vector-count to tx-count
    set tx-values to vector-ptr
    call 'expr-ops' using kernel-state transform-state input-expr result-expr
    goback.
end program expr-abstract.

identification division.
program-id. expr-level-params recursive.
data division.
local-storage section.
copy 'transform.cpy'.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 vector-count binary-long unsigned.
01 vector-ptr usage pointer.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr vector-count vector-ptr result-expr.
    move 4 to tx-mode
    move vector-count to tx-count
    set tx-values to vector-ptr
    call 'expr-ops' using kernel-state transform-state input-expr result-expr
    goback.
end program expr-level-params.

identification division.
program-id. expr-abstract-range recursive.
data division.
local-storage section.
01 prefix-count binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 range-count binary-long unsigned.
01 vector-count binary-long unsigned.
01 vector-ptr usage pointer.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr range-count vector-count
    vector-ptr result-expr.
    compute prefix-count = function min(range-count, vector-count)
    call 'expr-abstract' using kernel-state input-expr prefix-count
        vector-ptr result-expr
    goback.
end program expr-abstract-range.

identification division.
program-id. expr-replace recursive.
data division.
local-storage section.
copy 'transform.cpy'.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 callback-name pic x any length.
01 callback-context usage pointer.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr callback-name
    callback-context result-expr.
    move 5 to tx-mode
    move callback-name to tx-callback
    set tx-context to callback-context
    call 'expr-ops' using kernel-state transform-state input-expr result-expr
    goback.
end program expr-replace.

identification division.
program-id. expr-eqv.
data division.
linkage section.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 answer binary-char unsigned.
procedure division using lhs rhs answer.
    move 0 to answer
    if lhs = rhs move 1 to answer end-if
    goback.
end program expr-eqv.

identification division.
program-id. expr-data.
data division.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
01 hash-val binary-double unsigned.
01 loose-range binary-long unsigned.
01 has-fvars binary-char unsigned.
01 has-params binary-char unsigned.
procedure division using kernel-state input-expr hash-val loose-range
    has-fvars has-params.
    set address of expr-arena to expr-ptr
    move expr-hash(input-expr) to hash-val
    move expr-lbvr(input-expr) to loose-range
    move expr-has-fvar(input-expr) to has-fvars
    move expr-has-param(input-expr) to has-params
    goback.
end program expr-data.

*> Lean4Lean/Instantiate.lean: beta reduction only when no substitution is
*> required (a closed body, or a body that selects one supplied argument).
identification division.
program-id. expr-cheap-beta.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 args binary-long unsigned.
01 remaining binary-long unsigned.
01 arg-id binary-long unsigned.
01 next-id binary-long unsigned.
01 consumed binary-long unsigned.
01 index-val binary-long unsigned.
01 i binary-long unsigned.
01 app-kind binary-long unsigned value 3.
01 zero-val binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'list.cpy'.
01 input-expr binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr result-expr.
    move input-expr to current-id result-expr
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(current-id) not = 3 goback end-if
    perform until expr-kind(current-id) not = 3
        move expr-a(current-id) to current-id
    end-perform
    if expr-kind(current-id) not = 4 goback end-if
    move input-expr to current-id
    perform until expr-kind(current-id) not = 3 or verdict not = 0
        move expr-b(current-id) to arg-id
        move expr-a(current-id) to current-id
        call 'list-intern' using kernel-state arg-id args next-id
        move next-id to args
    end-perform
    if verdict not = 0 goback end-if
    set address of list-arena to list-ptr
    move args to remaining
    perform until remaining = 0 or expr-kind(current-id) not = 4
        add 1 to consumed
        move expr-b(current-id) to current-id
        move list-b(remaining) to remaining
    end-perform
    if expr-lbvr(current-id) not = 0
        if expr-kind(current-id) not = 0 goback end-if
        move expr-a(current-id) to index-val
        if index-val >= consumed move 3 to verdict goback end-if
        compute index-val = consumed - index-val - 1
        perform index-val times move list-b(args) to args end-perform
        move list-a(args) to current-id
    end-if
    perform until remaining = 0 or verdict not = 0
        move list-a(remaining) to arg-id
        move list-b(remaining) to remaining
        call 'expr-intern' using kernel-state app-kind current-id arg-id zero-val zero-val next-id
        move next-id to current-id
    end-perform
    move current-id to result-expr
    goback.
end program expr-cheap-beta.
