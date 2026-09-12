*> Structural helpers for Primitive.unfoldNatWellFounded. Local lists use
*> binder order, except the explicit mode-1 substitution inside telescopes.
identification division.
program-id. expr-instantiate-list.
data division.
local-storage section.
copy 'transform.cpy'.
01 buffer-ptr usage pointer.
01 buffer-cap binary-long unsigned.
01 count-val binary-long unsigned.
01 p binary-long unsigned.
01 i binary-long unsigned.
01 width binary-long unsigned value 8.
linkage section.
copy 'state.cpy'.
copy 'list.cpy'.
01 vector-data based.
   02 vector-item occurs 1 to 67108864 depending on buffer-cap.
      03 vector-key binary-long unsigned.
      03 vector-value binary-long unsigned.
01 input-expr binary-long unsigned.
01 input-list binary-long unsigned.
01 mode-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr input-list mode-val result-expr.
    move input-expr to result-expr
    if verdict not = 0 or input-list = 0 goback end-if
    set address of list-arena to list-ptr
    move list-length(input-list) to count-val
    call 'arena-reserve' using buffer-ptr buffer-cap count-val width verdict
    if verdict not = 0 goback end-if
    set address of vector-data to buffer-ptr
    move input-list to p
    perform varying i from 1 by 1 until i > count-val
        move list-a(p) to vector-value(i) move list-b(p) to p
    end-perform
    move mode-val to tx-mode move count-val to tx-count
    set tx-values to buffer-ptr
    call 'expr-ops' using kernel-state transform-state input-expr result-expr
    call 'arena-release' using buffer-ptr
    goback.
end program expr-instantiate-list.

identification division.
program-id. primitive-telescope.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 domain-id binary-long unsigned.
01 instantiated binary-long unsigned.
01 local-id binary-long unsigned.
01 backwards binary-long unsigned.
01 tmp binary-long unsigned.
01 zero-val binary-long unsigned.
01 direct-mode binary-long unsigned value 1.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
01 binder-kind binary-long unsigned.
01 locals-list binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr binder-kind locals-list result-expr.
    move 0 to locals-list move input-expr to current-id result-expr
    perform until verdict not = 0
        set address of expr-arena to expr-ptr
        if expr-kind(current-id) not = binder-kind exit perform end-if
        move expr-a(current-id) to domain-id move expr-b(current-id) to current-id
        call 'expr-instantiate-list' using kernel-state domain-id backwards direct-mode instantiated
        call 'local-fresh' using kernel-state instantiated zero-val local-id
        call 'list-intern' using kernel-state local-id backwards tmp move tmp to backwards
    end-perform
    call 'expr-instantiate-list' using kernel-state current-id backwards direct-mode result-expr
    call 'list-reverse' using kernel-state backwards locals-list
    goback.
end program primitive-telescope.

identification division.
program-id. expr-replace-exact.
data division.
local-storage section.
01 context-data.
   02 old-id binary-long unsigned.
   02 new-id binary-long unsigned.
01 context-ptr usage pointer.
01 callback-name pic x(64) value 'replace-exact-callback'.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 old-expr binary-long unsigned.
01 new-expr binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr old-expr new-expr result-expr.
    move old-expr to old-id move new-expr to new-id
    set context-ptr to address of context-data
    call 'expr-replace' using kernel-state input-expr callback-name context-ptr result-expr
    goback.
end program expr-replace-exact.

identification division.
program-id. replace-exact-callback.
data division.
linkage section.
copy 'state.cpy'.
01 context-ptr usage pointer.
01 context-data based.
   02 old-id binary-long unsigned.
   02 new-id binary-long unsigned.
01 input-expr binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state context-ptr input-expr result-expr.
    move 0 to result-expr
    set address of context-data to context-ptr
    if input-expr = old-id move new-id to result-expr end-if
    goback.
end program replace-exact-callback.
