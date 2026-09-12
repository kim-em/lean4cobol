*> whnfCore performs beta/zeta reduction. whnf additionally unfolds delta
*> heads. Recursors and projections delegate to their dedicated modules;
*> Nat arithmetic delegates to decimal limbs; strings expand on demand.
identification division.
program-id. weak-head-core-body recursive.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 body-id binary-long unsigned.
01 fn-id binary-long unsigned.
01 new-id binary-long unsigned.
01 zero-val binary-long unsigned.
01 next-depth binary-long unsigned.
01 family binary-long unsigned value 3.
01 ignored binary-long unsigned.
01 save-result binary-char unsigned.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 pending binary-long unsigned.
01 arg-id binary-long unsigned.
01 tmp binary-long unsigned.
01 one-val binary-long unsigned value 1.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'declarations.cpy'.
copy 'list.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-expr.
    move input-expr to current-id result-expr
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    set address of expr-arena to expr-ptr
    move expr-kind(current-id) to k
    move expr-a(current-id) to a move expr-b(current-id) to b
    move expr-c(current-id) to body-id
    evaluate k
      when 0 when 1 when 2 when 4 when 5 when 8 when 9 goback
      when 11
        call 'weak-head-core-body' using kernel-state a next-depth result-expr goback
      when 10
        set address of local-arena to local-ptr
        move local-value(a) to new-id
        if new-id = 0 goback end-if
        call 'weak-head-core-impl' using kernel-state new-id next-depth result-expr goback
    end-evaluate
    call 'tc-cache' using kernel-state family current-id zero-val zero-val new-id
    if new-id not = 0 move new-id to result-expr goback end-if
    evaluate k
      when 6
        call 'expr-instantiate1' using kernel-state body-id b new-id
        call 'weak-head-core-impl' using kernel-state new-id next-depth result-expr
        move 1 to save-result
      when 3
        call 'expr-spine' using kernel-state current-id head-id args
        call 'weak-head-core-impl' using kernel-state head-id next-depth fn-id
        if verdict not = 0 goback end-if
        set address of expr-arena to expr-ptr
        if expr-kind(fn-id) = 4
            move fn-id to body-id
            perform until args = 0 or verdict not = 0
                set address of expr-arena to expr-ptr
                if expr-kind(body-id) not = 4 exit perform end-if
                move expr-b(body-id) to body-id
                set address of list-arena to list-ptr
                move list-a(args) to arg-id move list-b(args) to args
                call 'list-intern' using kernel-state arg-id pending tmp move tmp to pending
            end-perform
            call 'expr-instantiate-list' using kernel-state body-id pending one-val tmp
            call 'expr-app-list' using kernel-state tmp args new-id
            call 'weak-head-core-impl' using kernel-state new-id next-depth result-expr
            move 1 to save-result
        else
            if head-id not = fn-id
                call 'expr-app-list' using kernel-state fn-id args new-id
                call 'weak-head-core-impl' using kernel-state new-id next-depth result-expr
                move 1 to save-result
            else
                call 'ind-reduce' using kernel-state current-id next-depth new-id
                if new-id not = 0
                    call 'weak-head-core-impl' using kernel-state new-id next-depth result-expr
                end-if
            end-if
        end-if
      when 7
        call 'reduce-projection' using kernel-state body-id b next-depth new-id
        if new-id not = 0
            call 'weak-head-core-impl' using kernel-state new-id next-depth result-expr
        end-if
        move 1 to save-result
      when other move 2 to verdict
    end-evaluate
    if save-result = 1 and tc-cheap-proj = 0
        call 'tc-cache' using kernel-state family current-id zero-val result-expr ignored
    end-if
    goback.
end program weak-head-core-body.

identification division.
program-id. delta-info.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 n binary-long unsigned.
01 us binary-long unsigned.
01 ps binary-long unsigned.
01 dc binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'names.cpy'.
copy 'declarations.cpy'.
copy 'list.cpy'.
01 input-expr binary-long unsigned.
01 declaration-id binary-long unsigned.
procedure division using kernel-state input-expr declaration-id.
    move 0 to declaration-id
    if verdict not = 0 goback end-if
    move input-expr to current-id
    set address of expr-arena to expr-ptr
    perform until expr-kind(current-id) not = 3
        move expr-a(current-id) to current-id
    end-perform
    if expr-kind(current-id) not = 2 goback end-if
    move expr-a(current-id) to n
    move expr-b(current-id) to us
    set address of name-arena to name-ptr
    move name-env(n) to dc
    if dc = 0 goback end-if
    set address of decl-arena to decl-ptr
    if decl-kind(dc) not = 1 and decl-kind(dc) not = 2 goback end-if
    move decl-params(dc) to ps
    if ps = 0 or us = 0
        if ps not = us goback end-if
    else
        set address of list-arena to list-ptr
        if list-length(ps) not = list-length(us) goback end-if
    end-if
    move dc to declaration-id
    goback.
end program delta-info.

identification division.
program-id. unfold-head recursive.
data division.
local-storage section.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 dc binary-long unsigned.
01 ty binary-long unsigned.
01 ps binary-long unsigned.
01 fn-id binary-long unsigned.
01 next-depth binary-long unsigned.
01 zero-val binary-long unsigned.
01 family binary-long unsigned value 5.
01 ignored binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'declarations.cpy'.
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
    move expr-kind(input-expr) to k
    move expr-a(input-expr) to a move expr-b(input-expr) to b
    evaluate k
      when 3
        call 'unfold-head' using kernel-state a next-depth fn-id
        if fn-id not = 0
            call 'expr-intern' using kernel-state k fn-id b zero-val zero-val result-expr
        end-if
      when 2
        call 'delta-info' using kernel-state input-expr dc
        if dc = 0 goback end-if
        if b not = 0
            call 'tc-cache' using kernel-state family input-expr zero-val zero-val result-expr
            if result-expr not = 0 goback end-if
        end-if
        set address of decl-arena to decl-ptr
        move decl-value(dc) to ty move decl-params(dc) to ps
        call 'instantiate-constant-type' using kernel-state ty ps b result-expr
        if b not = 0
            call 'tc-cache' using kernel-state family input-expr zero-val result-expr ignored
        end-if
    end-evaluate
    goback.
end program unfold-head.

identification division.
program-id. weak-head-body recursive.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 new-id binary-long unsigned.
01 next-depth binary-long unsigned.
01 zero-val binary-long unsigned.
01 loops binary-long unsigned.
01 loop-limit binary-long unsigned.
01 family binary-long unsigned value 4.
01 ignored binary-long unsigned.
01 k binary-long unsigned.
01 a binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'declarations.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-expr.
    move input-expr to current-id result-expr
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    set address of expr-arena to expr-ptr
    move expr-kind(current-id) to k move expr-a(current-id) to a
    evaluate k
      when 0 when 1 when 5 when 8 when 9 goback
      when 11 call 'weak-head-body' using kernel-state a next-depth result-expr goback
      when 10
        set address of local-arena to local-ptr
        if local-value(a) = 0 goback end-if
    end-evaluate
    call 'tc-cache' using kernel-state family current-id zero-val zero-val new-id
    if new-id not = 0 move new-id to result-expr goback end-if
    move fuel-whnf to loop-limit
    if tc-eager = 1 move fuel-whnf-eager to loop-limit end-if
    perform until verdict not = 0
        if loops >= loop-limit move 2 to verdict goback end-if
        add 1 to loops
        call 'weak-head-core-direct' using kernel-state current-id next-depth new-id
        move new-id to current-id
        call 'reduce-native' using kernel-state current-id
        call 'reduce-nat' using kernel-state current-id next-depth new-id
        if new-id not = 0 move new-id to current-id exit perform end-if
        call 'unfold-head' using kernel-state current-id next-depth new-id
        if new-id = 0 exit perform end-if
        move new-id to current-id
    end-perform
    move current-id to result-expr
    call 'tc-cache' using kernel-state family input-expr zero-val result-expr ignored
    goback.
end program weak-head-body.

identification division.
program-id. weak-head-core recursive.
data division.
local-storage section.
01 saved-mode binary-char unsigned.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-expr.
    move tc-cheap-proj to saved-mode
    move 0 to tc-cheap-proj
    call 'weak-head-core-impl' using kernel-state input-expr depth-val result-expr
    move saved-mode to tc-cheap-proj
    goback.
end program weak-head-core.

identification division.
program-id. weak-head-cheap recursive.
data division.
local-storage section.
01 saved-mode binary-char unsigned.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-expr.
    move tc-cheap-proj to saved-mode
    move 1 to tc-cheap-proj
    call 'weak-head-core-impl' using kernel-state input-expr depth-val result-expr
    move saved-mode to tc-cheap-proj
    goback.
end program weak-head-cheap.
