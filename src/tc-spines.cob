*> Delayed substitutions for TypeChecker.inferLambda/inferForall/inferLet,
*> inferApp, and isDefEqLambda/isDefEqForall. Pending lists are nearest-first.
identification division.
program-id. infer-binding-spine recursive.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 binder-kind binary-long unsigned.
01 domain-id binary-long unsigned.
01 value-id binary-long unsigned.
01 instantiated binary-long unsigned.
01 local-id binary-long unsigned.
01 backwards binary-long unsigned.
01 locals-list binary-long unsigned.
01 universes binary-long unsigned.
01 universe-id binary-long unsigned.
01 body-universe binary-long unsigned.
01 tmp binary-long unsigned.
01 ty binary-long unsigned.
01 zero-val binary-long unsigned.
01 one-val binary-long unsigned value 1.
01 forall-kind binary-long unsigned value 5.
01 imax-kind binary-long unsigned value 3.
01 equal-val binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'list.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-type binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-type.
    move 0 to result-type
    move input-expr to current-id
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    move expr-kind(current-id) to binder-kind
    perform until verdict not = 0
        set address of expr-arena to expr-ptr
        if expr-kind(current-id) not = binder-kind exit perform end-if
        move expr-a(current-id) to domain-id
        if binder-kind = 6
            move expr-b(current-id) to value-id
            move expr-c(current-id) to current-id
        else
            move expr-b(current-id) to current-id
        end-if
        call 'expr-instantiate-list' using kernel-state domain-id backwards one-val instantiated
        move instantiated to domain-id
        if binder-kind = 5 or tc-infer-only = 0
            call 'infer-sort' using kernel-state domain-id depth-val universe-id
        end-if
        if binder-kind = 5
            call 'list-intern' using kernel-state universe-id universes tmp
            move tmp to universes
        end-if
        if binder-kind = 6
            call 'expr-instantiate-list' using kernel-state value-id backwards one-val instantiated
            move instantiated to value-id
            if tc-infer-only = 0
                call 'infer-type' using kernel-state value-id depth-val ty
                call 'def-equal' using kernel-state ty domain-id depth-val equal-val
                if verdict = 0 and equal-val = 0 move 1 to verdict end-if
            end-if
        end-if
        if verdict not = 0 goback end-if
        call 'local-fresh' using kernel-state domain-id value-id local-id
        call 'list-intern' using kernel-state local-id backwards tmp
        move tmp to backwards
    end-perform
    call 'expr-instantiate-list' using kernel-state current-id backwards one-val instantiated
    if binder-kind = 5
        call 'infer-sort' using kernel-state instantiated depth-val body-universe
        perform until universes = 0 or verdict not = 0
            set address of list-arena to list-ptr
            move list-a(universes) to universe-id move list-b(universes) to universes
            call 'level-make' using kernel-state imax-kind universe-id body-universe tmp
            move tmp to body-universe
        end-perform
        call 'expr-intern' using kernel-state one-val body-universe zero-val zero-val zero-val result-type
    else
        call 'infer-type' using kernel-state instantiated depth-val ty
        call 'expr-cheap-beta' using kernel-state ty instantiated
        call 'list-reverse' using kernel-state backwards locals-list
        call 'expr-bind-list' using kernel-state forall-kind locals-list instantiated result-type
    end-if
    goback.
end program infer-binding-spine.

identification division.
program-id. infer-app-spine recursive.
data division.
local-storage section.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 arg-id binary-long unsigned.
01 pending binary-long unsigned.
01 current-type binary-long unsigned.
01 instantiated binary-long unsigned.
01 tmp binary-long unsigned.
01 one-val binary-long unsigned value 1.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'list.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-type binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-type.
    move 0 to result-type
    call 'expr-spine' using kernel-state input-expr head-id args
    call 'infer-type' using kernel-state head-id depth-val current-type
    perform until args = 0 or verdict not = 0
        set address of expr-arena to expr-ptr
        if expr-kind(current-type) not = 5
            call 'expr-instantiate-list' using kernel-state current-type pending one-val instantiated
            move 0 to pending
            call 'weak-head' using kernel-state instantiated depth-val current-type
            if verdict not = 0 goback end-if
            set address of expr-arena to expr-ptr
            if expr-kind(current-type) not = 5 move 1 to verdict goback end-if
        end-if
        move expr-b(current-type) to current-type
        set address of list-arena to list-ptr
        move list-a(args) to arg-id move list-b(args) to args
        call 'list-intern' using kernel-state arg-id pending tmp move tmp to pending
    end-perform
    call 'expr-instantiate-list' using kernel-state current-type pending one-val result-type
    goback.
end program infer-app-spine.

identification division.
program-id. def-binding-spine recursive.
data division.
local-storage section.
01 left-id binary-long unsigned.
01 right-id binary-long unsigned.
01 left-domain binary-long unsigned.
01 right-domain binary-long unsigned.
01 left-body binary-long unsigned.
01 right-body binary-long unsigned.
01 left-type binary-long unsigned.
01 right-type binary-long unsigned.
01 pending binary-long unsigned.
01 local-id binary-long unsigned.
01 tmp binary-long unsigned.
01 binder-kind binary-long unsigned.
01 zero-val binary-long unsigned.
01 one-val binary-long unsigned value 1.
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
    move lhs to left-id move rhs to right-id
    set address of expr-arena to expr-ptr
    move expr-kind(lhs) to binder-kind
    perform until verdict not = 0
        set address of expr-arena to expr-ptr
        if expr-kind(left-id) not = binder-kind or expr-kind(right-id) not = binder-kind
            exit perform
        end-if
        move expr-a(left-id) to left-domain move expr-b(left-id) to left-body
        move expr-a(right-id) to right-domain move expr-b(right-id) to right-body
        move 0 to right-type
        if left-domain not = right-domain
            call 'expr-instantiate-list' using kernel-state right-domain pending one-val right-type
            call 'expr-instantiate-list' using kernel-state left-domain pending one-val left-type
            call 'def-equal' using kernel-state left-type right-type depth-val answer
            if answer = 0 or verdict not = 0 goback end-if
        end-if
        set address of expr-arena to expr-ptr
        if expr-lbvr(left-body) not = 0 or expr-lbvr(right-body) not = 0
            if right-type = 0
                call 'expr-instantiate-list' using kernel-state right-domain pending one-val right-type
            end-if
            call 'local-fresh' using kernel-state right-type zero-val local-id
        else
            *> This placeholder cannot occur in either closed body.
            call 'expr-intern' using kernel-state one-val one-val zero-val zero-val zero-val local-id
        end-if
        call 'list-intern' using kernel-state local-id pending tmp move tmp to pending
        move left-body to left-id move right-body to right-id
    end-perform
    call 'expr-instantiate-list' using kernel-state left-id pending one-val left-type
    call 'expr-instantiate-list' using kernel-state right-id pending one-val right-type
    call 'def-equal' using kernel-state left-type right-type depth-val answer
    goback.
end program def-binding-spine.
