*> Helpers for the inductive/quotient expression builders. Argument and local
*> lists are in binder/application order. All inputs are closed over fvars.
identification division.
program-id. expr-spine.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 arg-id binary-long unsigned.
01 args binary-long unsigned.
01 next-id binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
01 head-expr binary-long unsigned.
01 args-list binary-long unsigned.
procedure division using kernel-state input-expr head-expr args-list.
    move input-expr to current-id
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    perform until expr-kind(current-id) not = 3 or verdict not = 0
        move expr-b(current-id) to arg-id move expr-a(current-id) to current-id
        call 'list-intern' using kernel-state arg-id args next-id
        move next-id to args
    end-perform
    move current-id to head-expr move args to args-list
    goback.
end program expr-spine.

identification division.
program-id. expr-app-list.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 current-list binary-long unsigned.
01 arg-id binary-long unsigned.
01 next-id binary-long unsigned.
01 zero-val binary-long unsigned.
01 app-kind binary-long unsigned value 3.
linkage section.
copy 'state.cpy'.
copy 'list.cpy'.
01 input-expr binary-long unsigned.
01 args-list binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr args-list result-expr.
    move input-expr to current-id move args-list to current-list
    perform until current-list = 0 or verdict not = 0
        set address of list-arena to list-ptr
        move list-a(current-list) to arg-id move list-b(current-list) to current-list
        call 'expr-intern' using kernel-state app-kind current-id arg-id zero-val zero-val next-id
        move next-id to current-id
    end-perform
    move current-id to result-expr
    goback.
end program expr-app-list.

identification division.
program-id. expr-bind-list.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 current-list binary-long unsigned.
01 local-id binary-long unsigned.
01 domain-id binary-long unsigned.
01 value-id binary-long unsigned.
01 abstracted binary-long unsigned.
01 next-id binary-long unsigned.
01 zero-val binary-long unsigned.
01 one-val binary-long unsigned value 1.
01 let-kind binary-long unsigned value 6.
01 vector-item.
   02 vector-key binary-long unsigned.
   02 vector-value binary-long unsigned.
01 vector-ptr usage pointer.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'list.cpy'.
copy 'declarations.cpy'.
01 binding-kind binary-long unsigned.
01 locals-list binary-long unsigned.
01 input-expr binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state binding-kind locals-list input-expr result-expr.
    move input-expr to current-id result-expr
    call 'list-reverse' using kernel-state locals-list current-list
    set vector-ptr to address of vector-item
    perform until current-list = 0 or verdict not = 0
        set address of list-arena to list-ptr
        move list-a(current-list) to vector-value
        move list-b(current-list) to current-list
        set address of expr-arena to expr-ptr
        if expr-kind(vector-value) not = 10 move 3 to verdict exit perform end-if
        move expr-a(vector-value) to local-id
        set address of local-arena to local-ptr
        move local-type(local-id) to domain-id move local-value(local-id) to value-id
        call 'expr-abstract' using kernel-state current-id one-val vector-ptr abstracted
        if verdict not = 0 exit perform end-if
        if value-id = 0
            call 'expr-intern' using kernel-state binding-kind domain-id abstracted zero-val zero-val next-id
            move next-id to current-id
        else
            set address of expr-arena to expr-ptr
            if expr-lbvr(abstracted) not = 0
                call 'expr-intern' using kernel-state let-kind domain-id value-id abstracted zero-val next-id
                move next-id to current-id
            end-if
        end-if
    end-perform
    move current-id to result-expr
    goback.
end program expr-bind-list.

*> Inductive/Add.lean consumes type annotation gadgets when creating locals.
*> Other type-checker locals retain their original domain expressions.
identification division.
program-id. ind-local-fresh.
data division.
local-storage section.
01 stripped binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 ty binary-long unsigned.
01 val binary-long unsigned.
01 result-id binary-long unsigned.
procedure division using kernel-state ty val result-id.
    call 'expr-consume-type-annotations' using kernel-state ty stripped
    call 'local-fresh' using kernel-state stripped val result-id
    goback.
end program ind-local-fresh.

identification division.
program-id. expr-consume-type-annotations.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 name-id binary-long unsigned.
01 arg-count binary-long unsigned.
01 zero-val binary-long unsigned.
01 matched binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'list.cpy'.
01 input-expr binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr result-expr.
    move input-expr to current-id result-expr
    perform until verdict not = 0
        call 'expr-spine' using kernel-state current-id head-id args
        if verdict not = 0 or args = 0 exit perform end-if
        set address of expr-arena to expr-ptr
        if expr-kind(head-id) not = 2 exit perform end-if
        move expr-a(head-id) to name-id
        set address of list-arena to list-ptr move list-length(args) to arg-count
        move 0 to matched
        evaluate arg-count
          when 1
            call 'name-matches' using kernel-state name-id 'outParam' matched
            if matched = 0 call 'name-matches' using kernel-state name-id 'semiOutParam' matched end-if
          when 2
            call 'name-matches' using kernel-state name-id 'optParam' matched
            if matched = 0 call 'name-matches' using kernel-state name-id 'autoParam' matched end-if
        end-evaluate
        if matched = 0 exit perform end-if
        call 'list-nth' using kernel-state args zero-val current-id
    end-perform
    move current-id to result-expr
    goback.
end program expr-consume-type-annotations.
