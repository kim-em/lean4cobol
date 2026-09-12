*> TypeChecker.isDefEq: quick comparison, reduction, proof irrelevance,
*> lazy delta, congruence, function/structure eta, and unit-like equality.
*> Nat literal reduction follows the reference lazy-delta guards.
identification division.
program-id. def-equal recursive.
data division.
local-storage section.
01 left-id binary-long unsigned.
01 right-id binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 depth-val binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs depth-val answer.
    move lhs to left-id move rhs to right-id
    call 'def-equal-core' using kernel-state left-id right-id depth-val answer
    if verdict = 0 and answer = 1
        call 'equiv-merge' using kernel-state left-id right-id
    end-if
    goback.
end program def-equal.

identification division.
program-id. def-quick recursive.
data division.
local-storage section.
01 lk binary-long unsigned.
01 rk binary-long unsigned.
01 la binary-long unsigned.
01 lb binary-long unsigned.
01 ra binary-long unsigned.
01 rb binary-long unsigned.
01 li binary-long unsigned.
01 ri binary-long unsigned.
01 local-id binary-long unsigned.
01 zero-val binary-long unsigned.
01 next-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 use-hash binary-char unsigned.
01 depth-val binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs use-hash depth-val answer.
    move 2 to answer
    if verdict not = 0 goback end-if
    call 'equiv-test' using kernel-state lhs rhs use-hash depth-val answer
    if answer = 1 or verdict not = 0 goback end-if
    move 2 to answer
    move depth-val to next-depth
    add 1 to next-depth
    set address of expr-arena to expr-ptr
    move expr-kind(lhs) to lk move expr-kind(rhs) to rk
    move expr-a(lhs) to la move expr-b(lhs) to lb
    move expr-a(rhs) to ra move expr-b(rhs) to rb
    if lk = rk
        evaluate lk
          when 1 call 'level-native-equal' using kernel-state la ra answer
          when 4 when 5
            call 'def-binding-spine' using kernel-state lhs rhs next-depth answer
          when 11 call 'def-equal' using kernel-state la ra next-depth answer
          when 8 when 9
            move 0 to answer if la = ra move 1 to answer end-if
        end-evaluate
    else
        if (lk = 8 or lk = 9) and (rk = 8 or rk = 9) move 0 to answer end-if
    end-if
    goback.
end program def-quick.

identification division.
program-id. constant-levels-equal.
data division.
local-storage section.
01 left-id binary-long unsigned.
01 right-id binary-long unsigned.
01 p binary-long unsigned.
01 q binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 zero-val binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'list.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs answer.
    move 0 to answer
    if verdict not = 0 goback end-if
    move lhs to left-id move rhs to right-id
    set address of expr-arena to expr-ptr
    perform until expr-kind(left-id) not = 3 move expr-a(left-id) to left-id end-perform
    perform until expr-kind(right-id) not = 3 move expr-a(right-id) to right-id end-perform
    if expr-kind(left-id) not = 2 or expr-kind(right-id) not = 2 goback end-if
    if expr-a(left-id) not = expr-a(right-id) goback end-if
    move expr-b(left-id) to p move expr-b(right-id) to q
    perform until p = 0 or q = 0 or verdict not = 0
        set address of list-arena to list-ptr
        move list-a(p) to a move list-a(q) to b
        move list-b(p) to p move list-b(q) to q
        call 'level-compare' using kernel-state a b zero-val answer
        if answer = 0 goback end-if
    end-perform
    move 0 to answer
    if p = q and verdict = 0 move 1 to answer end-if
    goback.
end program constant-levels-equal.

identification division.
program-id. def-args-reverse recursive.
data division.
local-storage section.
01 la binary-long unsigned.
01 lb binary-long unsigned.
01 ra binary-long unsigned.
01 rb binary-long unsigned.
01 next-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 depth-val binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs depth-val answer.
    move 0 to answer
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(lhs) not = 3 or expr-kind(rhs) not = 3
        if expr-kind(lhs) not = 3 and expr-kind(rhs) not = 3 move 1 to answer end-if
        goback
    end-if
    move depth-val to next-depth
    add 1 to next-depth
    move expr-a(lhs) to la move expr-b(lhs) to lb
    move expr-a(rhs) to ra move expr-b(rhs) to rb
    call 'def-equal' using kernel-state lb rb next-depth answer
    if answer = 1 and verdict = 0
        call 'def-args-reverse' using kernel-state la ra next-depth answer
    end-if
    goback.
end program def-args-reverse.

identification division.
program-id. lazy-delta recursive.
data division.
local-storage section.
01 left-id binary-long unsigned.
01 right-id binary-long unsigned.
01 loops binary-long unsigned.
01 new-id binary-long unsigned.
01 next-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 depth-val binary-long unsigned.
01 left-out binary-long unsigned.
01 right-out binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs depth-val left-out right-out answer.
    move lhs to left-id move rhs to right-id
    move 2 to answer
    if verdict not = 0 goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    perform until verdict not = 0
        if loops >= fuel-lazy-delta move 2 to verdict exit perform end-if
        add 1 to loops
        call 'def-nat-offset' using kernel-state left-id right-id next-depth answer
        if answer not = 2 or verdict not = 0 exit perform end-if
        set address of expr-arena to expr-ptr
        if (expr-has-fvar(left-id) = 0 and expr-has-fvar(right-id) = 0) or tc-eager = 1
            call 'reduce-nat' using kernel-state left-id next-depth new-id
            if new-id not = 0
                move new-id to left-id
                call 'def-equal-core' using kernel-state left-id right-id next-depth answer
                exit perform
            end-if
            call 'reduce-nat' using kernel-state right-id next-depth new-id
            if new-id not = 0
                move new-id to right-id
                call 'def-equal-core' using kernel-state left-id right-id next-depth answer
                exit perform
            end-if
        end-if
        call 'reduce-native' using kernel-state left-id
        call 'reduce-native' using kernel-state right-id
        if verdict not = 0 exit perform end-if
        call 'lazy-delta-step' using kernel-state left-id right-id next-depth left-out right-out answer
        move left-out to left-id move right-out to right-id
        if answer not = 3 exit perform end-if
        move 2 to answer
    end-perform
    move left-id to left-out move right-id to right-out
    goback.
end program lazy-delta.

identification division.
program-id. lazy-delta-step recursive.
data division.
local-storage section.
01 left-id binary-long unsigned.
01 right-id binary-long unsigned.
01 ld binary-long unsigned.
01 right-decl binary-long unsigned.
01 lp binary-long unsigned.
01 rp binary-long unsigned.
01 lh binary-long unsigned.
01 right-height binary-long unsigned.
01 new-id binary-long unsigned.
01 key-a binary-long unsigned.
01 key-b binary-long unsigned.
01 failed binary-long unsigned.
01 next-depth binary-long unsigned.
01 zero-val binary-long unsigned.
01 one-val binary-long unsigned value 1.
01 family binary-long unsigned value 6.
01 use-hash binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'declarations.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 depth-val binary-long unsigned.
01 left-out binary-long unsigned.
01 right-out binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs depth-val left-out right-out answer.
    move lhs to left-id left-out move rhs to right-id right-out
    move 2 to answer
    if verdict not = 0 goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    call 'delta-info' using kernel-state left-id ld
    call 'delta-info' using kernel-state right-id right-decl
    if ld = 0 and right-decl = 0 goback end-if
    if ld not = 0 and right-decl = 0
        call 'try-unfold-projection-app' using kernel-state right-id next-depth new-id
        if new-id not = 0
            move new-id to right-id perform continue-step goback
        end-if
    end-if
    if ld = 0 and right-decl not = 0
        call 'try-unfold-projection-app' using kernel-state left-id next-depth new-id
        if new-id not = 0
            move new-id to left-id perform continue-step goback
        end-if
    end-if
    if ld not = 0 and right-decl not = 0
        set address of decl-arena to decl-ptr
        move decl-hints(ld) to lp move decl-hints(right-decl) to rp
        *> opaque < regular < abbrev; regular heights break ties.
        evaluate lp when 1 move 2 to lp when 2 move 1 to lp end-evaluate
        evaluate rp when 1 move 2 to rp when 2 move 1 to rp end-evaluate
        move decl-height(ld) to lh move decl-height(right-decl) to right-height
        if lp < rp or (lp = 1 and rp = 1 and lh < right-height)
            move 0 to ld
        else
            if rp < lp or (lp = 1 and rp = 1 and right-height < lh)
                move 0 to right-decl
            else
                set address of expr-arena to expr-ptr
                if ld = right-decl and lp = 1 and expr-kind(left-id) = 3 and expr-kind(right-id) = 3
                    compute key-a = function min(left-id, right-id)
                    compute key-b = function max(left-id, right-id)
                    call 'tc-cache' using kernel-state family key-a key-b zero-val failed
                    if failed = 0
                        call 'constant-levels-equal' using kernel-state left-id right-id answer
                        if answer = 1
                            call 'def-args-reverse' using kernel-state left-id right-id next-depth answer
                        end-if
                        if answer = 1 or verdict not = 0 perform finish-step goback end-if
                        call 'tc-cache' using kernel-state family key-a key-b one-val failed
                        move 2 to answer
                    end-if
                end-if
            end-if
        end-if
    end-if
    if ld not = 0
        call 'unfold-head' using kernel-state left-id next-depth new-id
        call 'weak-head-cheap' using kernel-state new-id next-depth left-id
    end-if
    if right-decl not = 0
        call 'unfold-head' using kernel-state right-id next-depth new-id
        call 'weak-head-cheap' using kernel-state new-id next-depth right-id
    end-if
    perform continue-step
    goback.
continue-step.
    call 'def-quick' using kernel-state left-id right-id use-hash next-depth answer
    if answer = 2 move 3 to answer end-if
    perform finish-step.
finish-step.
    move left-id to left-out move right-id to right-out.
end program lazy-delta-step.

identification division.
program-id. def-app recursive.
data division.
local-storage section.
01 left-id binary-long unsigned.
01 right-id binary-long unsigned.
01 lp binary-long unsigned.
01 rp binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 new-list binary-long unsigned.
01 next-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'list.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 depth-val binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs depth-val answer.
    move 0 to answer
    if verdict not = 0 goback end-if
    move lhs to left-id move rhs to right-id
    set address of expr-arena to expr-ptr
    if expr-kind(lhs) not = 3 or expr-kind(rhs) not = 3 goback end-if
    perform until expr-kind(left-id) not = 3 or verdict not = 0
        move expr-b(left-id) to a move expr-a(left-id) to left-id
        call 'list-intern' using kernel-state a lp new-list
        move new-list to lp
    end-perform
    perform until expr-kind(right-id) not = 3 or verdict not = 0
        move expr-b(right-id) to a move expr-a(right-id) to right-id
        call 'list-intern' using kernel-state a rp new-list
        move new-list to rp
    end-perform
    if verdict not = 0 goback end-if
    set address of list-arena to list-ptr
    if list-length(lp) not = list-length(rp) goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    call 'def-equal' using kernel-state left-id right-id next-depth answer
    perform until lp = 0 or answer = 0 or verdict not = 0
        set address of list-arena to list-ptr
        move list-a(lp) to a move list-a(rp) to b
        move list-b(lp) to lp move list-b(rp) to rp
        call 'def-equal' using kernel-state a b next-depth answer
    end-perform
    goback.
end program def-app.

identification division.
program-id. def-eta recursive.
data division.
local-storage section.
01 ty binary-long unsigned.
01 normalized binary-long unsigned.
01 domain-id binary-long unsigned.
01 bvar-id binary-long unsigned.
01 app-id binary-long unsigned.
01 lambda-id binary-long unsigned.
01 zero-val binary-long unsigned.
01 app-kind binary-long unsigned value 3.
01 lam-kind binary-long unsigned value 4.
01 next-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 depth-val binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs depth-val answer.
    move 0 to answer
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(lhs) not = 4 or expr-kind(rhs) = 4 goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    call 'infer-only' using kernel-state rhs next-depth ty
    call 'weak-head' using kernel-state ty next-depth normalized
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(normalized) not = 5 goback end-if
    move expr-a(normalized) to domain-id
    call 'expr-intern' using kernel-state zero-val zero-val zero-val zero-val zero-val bvar-id
    call 'expr-intern' using kernel-state app-kind rhs bvar-id zero-val zero-val app-id
    call 'expr-intern' using kernel-state lam-kind domain-id app-id zero-val zero-val lambda-id
    call 'def-equal' using kernel-state lhs lambda-id next-depth answer
    goback.
end program def-eta.

identification division.
program-id. def-equal-body recursive.
data division.
local-storage section.
01 left-id binary-long unsigned.
01 right-id binary-long unsigned.
01 left-normal binary-long unsigned.
01 right-normal binary-long unsigned.
01 ty binary-long unsigned.
01 tyty binary-long unsigned.
01 normalized binary-long unsigned.
01 true-name binary-long unsigned.
01 true-match binary-char unsigned.
01 other-ty binary-long unsigned.
01 universe-id binary-long unsigned.
01 next-depth binary-long unsigned.
01 use-hash binary-char unsigned value 1.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'levels.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 depth-val binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs depth-val answer.
    move 0 to answer
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    call 'def-quick' using kernel-state lhs rhs use-hash next-depth answer
    if answer not = 2 or verdict not = 0 goback end-if
    *> Reference's closed/eager boolean shortcut runs before proof inference.
    set address of expr-arena to expr-ptr
    if (expr-has-fvar(lhs) = 0 or tc-eager = 1) and expr-kind(rhs) = 2
        move expr-a(rhs) to true-name
        call 'name-matches' using kernel-state true-name 'Bool.true' true-match
        if true-match = 1
            call 'weak-head' using kernel-state lhs next-depth normalized
            if verdict not = 0 goback end-if
            set address of expr-arena to expr-ptr
            if expr-kind(normalized) = 2
                move expr-a(normalized) to true-name
                call 'name-matches' using kernel-state true-name 'Bool.true' true-match
                if true-match = 1 move 1 to answer goback end-if
            end-if
        end-if
    end-if
    move 0 to use-hash
    call 'weak-head-cheap' using kernel-state lhs next-depth left-id
    call 'weak-head-cheap' using kernel-state rhs next-depth right-id
    if verdict not = 0 goback end-if
    if lhs not = left-id or rhs not = right-id
        call 'def-quick' using kernel-state left-id right-id use-hash next-depth answer
        if answer not = 2 or verdict not = 0 goback end-if
    end-if
    *> isDefEqProofIrrel: only types are compared once the lhs is a proof.
    call 'infer-only' using kernel-state left-id next-depth ty
    call 'infer-only' using kernel-state ty next-depth tyty
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr move tyty to normalized
    if expr-kind(tyty) not = 1
        call 'weak-head' using kernel-state tyty next-depth normalized
    end-if
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(normalized) not = 1 move 1 to verdict goback end-if
    move expr-a(normalized) to universe-id
    set address of level-arena to level-ptr
    if level-always-zero(universe-id) = 1
        call 'infer-only' using kernel-state right-id next-depth other-ty
        call 'def-equal' using kernel-state ty other-ty next-depth answer
        goback
    end-if
    call 'lazy-delta' using kernel-state left-id right-id next-depth left-normal right-normal answer
    if answer not = 2 or verdict not = 0 goback end-if
    move left-normal to left-id move right-normal to right-id
    set address of expr-arena to expr-ptr
    if expr-kind(left-id) = 2 and expr-kind(right-id) = 2
        call 'constant-levels-equal' using kernel-state left-id right-id answer
        if answer = 1 or verdict not = 0 goback end-if
    end-if
    set address of expr-arena to expr-ptr
    if expr-kind(left-id) = 7 and expr-kind(right-id) = 7
        if expr-b(left-id) = expr-b(right-id)
            move expr-b(left-id) to universe-id
            move expr-c(left-id) to ty move expr-c(right-id) to other-ty
            call 'lazy-delta-projection' using kernel-state ty other-ty universe-id next-depth answer
            if answer = 1 or verdict not = 0 goback end-if
        end-if
    end-if
    call 'weak-head-core' using kernel-state left-id next-depth left-normal
    call 'weak-head-core' using kernel-state right-id next-depth right-normal
    if left-normal not = left-id or right-normal not = right-id
        call 'def-equal-core' using kernel-state left-normal right-normal next-depth answer
        goback
    end-if
    call 'def-app' using kernel-state left-id right-id next-depth answer
    if answer = 1 or verdict not = 0 goback end-if
    call 'def-eta' using kernel-state left-id right-id next-depth answer
    if answer = 1 or verdict not = 0 goback end-if
    call 'def-eta' using kernel-state right-id left-id next-depth answer
    if answer = 1 or verdict not = 0 goback end-if
    call 'def-struct-core' using kernel-state left-id right-id next-depth answer
    if answer = 1 or verdict not = 0 goback end-if
    call 'def-struct-core' using kernel-state right-id left-id next-depth answer
    if answer = 1 or verdict not = 0 goback end-if
    call 'def-string-core' using kernel-state left-id right-id next-depth answer
    if answer not = 2 or verdict not = 0 goback end-if
    call 'def-string-core' using kernel-state right-id left-id next-depth answer
    if answer not = 2 or verdict not = 0 goback end-if
    call 'def-unit' using kernel-state left-id right-id next-depth answer
    goback.
end program def-equal-body.
