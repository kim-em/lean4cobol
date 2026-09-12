*> Dependent function core, proof irrelevance, eta, and lazy delta reduction.
*> Inductive/primitive and literal reduction are implemented in later modules.
identification division.
program-id. local-fresh.
data division.
local-storage section.
01 wanted binary-long unsigned.
01 width binary-long unsigned.
01 k binary-long unsigned value 10.
01 uid binary-long unsigned.
01 zero-val binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'declarations.cpy'.
01 ty binary-long unsigned.
01 val binary-long unsigned.
01 result-id binary-long unsigned.
procedure division using kernel-state ty val result-id.
    move local-count to wanted
    add 1 to wanted
    move length of local-node to width
    call 'arena-reserve' using local-ptr local-cap wanted width verdict
    if verdict not = 0 goback end-if
    set address of local-arena to local-ptr
    add 1 to local-count
    move local-count to uid
    move ty to local-type(uid)
    move val to local-value(uid)
    call 'expr-intern' using kernel-state k uid zero-val zero-val zero-val result-id
    goback.
end program local-fresh.

identification division.
program-id. infer-type-core recursive.
data division.
local-storage section.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 body-id binary-long unsigned.
01 ty binary-long unsigned.
01 arg-ty binary-long unsigned.
01 domain-id binary-long unsigned.
01 range-id binary-long unsigned.
01 local-id binary-long unsigned.
01 instantiated binary-long unsigned.
01 abstracted binary-long unsigned.
01 next-depth binary-long unsigned.
01 zero-val binary-long unsigned.
01 universe-a binary-long unsigned.
01 universe-b binary-long unsigned.
01 decl-id binary-long unsigned.
01 got binary-char unsigned.
01 eager-name binary-long unsigned.
01 eager-head binary-long unsigned.
01 saved-eager binary-char unsigned.
01 eager-arg binary-char unsigned.
01 one-val binary-long unsigned value 1.
01 substitution.
   02 subst-key binary-long unsigned.
   02 subst-value binary-long unsigned.
01 vector-ptr usage pointer.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'names.cpy'.
copy 'declarations.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-type binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-type.
    move 0 to result-type
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    set address of expr-arena to expr-ptr
    move expr-kind(input-expr) to k
    move expr-a(input-expr) to a
    move expr-b(input-expr) to b
    move expr-c(input-expr) to body-id
    evaluate k
      when 0 move 1 to verdict
      when 1
        call 'level-intern' using kernel-state one-val a zero-val universe-a
        call 'expr-intern' using kernel-state one-val universe-a zero-val
            zero-val zero-val result-type
      when 2
        set address of name-arena to name-ptr
        move name-env(a) to decl-id
        if decl-id = 0 move 1 to verdict goback end-if
        set address of decl-arena to decl-ptr
        if decl-status(decl-id) = 3 move 1 to verdict goback end-if
        move decl-type(decl-id) to ty
        move decl-params(decl-id) to domain-id
        call 'instantiate-constant-type' using kernel-state ty domain-id b result-type
      when 3
        if tc-infer-only = 1
            call 'infer-app-spine' using kernel-state input-expr next-depth result-type
            goback
        end-if
        call 'infer-type-impl' using kernel-state a next-depth ty
        if verdict not = 0 goback end-if
        set address of expr-arena to expr-ptr
        move ty to arg-ty
        if expr-kind(ty) not = 5
            call 'weak-head' using kernel-state ty next-depth arg-ty
        end-if
        if verdict not = 0 goback end-if
        set address of expr-arena to expr-ptr
        if expr-kind(arg-ty) not = 5 move 1 to verdict goback end-if
        move expr-a(arg-ty) to domain-id
        move expr-b(arg-ty) to range-id
        if tc-infer-only = 0
            call 'infer-type-impl' using kernel-state b next-depth ty
            move tc-eager to saved-eager
            set address of expr-arena to expr-ptr
            if expr-kind(b) = 3
                move expr-a(b) to eager-head
                if expr-kind(eager-head) = 3
                    move expr-a(eager-head) to eager-head
                    if expr-kind(eager-head) = 2
                        move expr-a(eager-head) to eager-name
                        call 'name-matches' using kernel-state eager-name 'eagerReduce' eager-arg
                        if eager-arg = 1 move 1 to tc-eager end-if
                    end-if
                end-if
            end-if
            call 'def-equal' using kernel-state domain-id ty next-depth got
            move saved-eager to tc-eager
            if verdict not = 0 goback end-if
            if got = 0 move 1 to verdict goback end-if
        end-if
        call 'expr-instantiate1' using kernel-state range-id b result-type
      when 4 when 5 when 6
        call 'infer-binding-spine' using kernel-state input-expr next-depth result-type
      when 8 when 9 call 'infer-literal' using kernel-state input-expr result-type
      when 7 call 'infer-projection' using kernel-state input-expr next-depth result-type
      when 10
        if a = 0 or a > local-count move 1 to verdict goback end-if
        set address of local-arena to local-ptr
        move local-type(a) to result-type
      when 11 call 'infer-type-impl' using kernel-state a next-depth result-type
      when other move 2 to verdict
    end-evaluate
    goback.
end program infer-type-core.

identification division.
program-id. infer-sort recursive.
data division.
local-storage section.
01 ty binary-long unsigned.
01 reduced binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-level binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-level.
    move 0 to result-level
    call 'infer-type' using kernel-state input-expr depth-val ty
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    move ty to reduced
    if expr-kind(ty) not = 1
        call 'weak-head' using kernel-state ty depth-val reduced
    end-if
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(reduced) not = 1 move 1 to verdict goback end-if
    move expr-a(reduced) to result-level
    goback.
end program infer-sort.

identification division.
program-id. infer-type-impl recursive.
data division.
local-storage section.
01 family binary-long unsigned.
01 zero-val binary-long unsigned.
01 ignored binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-type binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-type.
    move 0 to result-type
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-lbvr(input-expr) not = 0 move 1 to verdict goback end-if
    move 1 to family
    add tc-infer-only to family
    call 'tc-cache' using kernel-state family input-expr zero-val zero-val result-type
    if result-type not = 0 goback end-if
    call 'infer-type-core' using kernel-state input-expr depth-val result-type
    call 'tc-cache' using kernel-state family input-expr zero-val result-type ignored
    goback.
end program infer-type-impl.

identification division.
program-id. infer-only recursive.
data division.
local-storage section.
01 saved-mode binary-char unsigned.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-type binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-type.
    move tc-infer-only to saved-mode
    move 1 to tc-infer-only
    call 'infer-type' using kernel-state input-expr depth-val result-type
    move saved-mode to tc-infer-only
    goback.
end program infer-only.
