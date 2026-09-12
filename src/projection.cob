*> Projection typing/reduction and non-recursive structure support.
identification division.
program-id. type-sort-level recursive.
data division.
local-storage section.
01 ty binary-long unsigned.
01 normalized binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-level binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-level.
    move 0 to result-level
    call 'infer-only' using kernel-state input-expr depth-val ty
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr move ty to normalized
    if expr-kind(ty) not = 1
        call 'weak-head' using kernel-state ty depth-val normalized
    end-if
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(normalized) not = 1 move 1 to verdict goback end-if
    move expr-a(normalized) to result-level
    goback.
end program type-sort-level.

identification division.
program-id. nonrec-structure.
data division.
local-storage section.
01 d binary-long unsigned.
01 ctors binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'names.cpy'.
copy 'declarations.cpy'.
copy 'list.cpy'.
01 name-id binary-long unsigned.
01 result-id binary-long unsigned.
procedure division using kernel-state name-id result-id.
    move 0 to result-id
    if verdict not = 0 or name-id = 0 goback end-if
    set address of name-arena to name-ptr move name-env(name-id) to d
    if d = 0 goback end-if
    set address of decl-arena to decl-ptr
    if decl-kind(d) not = 4 or decl-is-rec(d) = 1 or decl-num-indices(d) not = 0 goback end-if
    move decl-ctors(d) to ctors
    if ctors = 0 goback end-if
    set address of list-arena to list-ptr
    if list-length(ctors) = 1 move d to result-id end-if
    goback.
end program nonrec-structure.

identification division.
program-id. reduce-projection recursive.
data division.
local-storage section.
01 normalized binary-long unsigned.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 name-id binary-long unsigned.
01 d binary-long unsigned.
01 index-val binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'names.cpy'.
copy 'declarations.cpy'.
01 struct-expr binary-long unsigned.
01 field-index binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state struct-expr field-index depth-val result-expr.
    move 0 to result-expr
    if tc-cheap-proj = 1
        call 'weak-head-cheap' using kernel-state struct-expr depth-val normalized
    else
        call 'weak-head' using kernel-state struct-expr depth-val normalized
    end-if
    call 'reduce-projection-core' using kernel-state normalized field-index depth-val result-expr
    goback.
end program reduce-projection.

identification division.
program-id. reduce-projection-core recursive.
data division.
local-storage section.
01 normalized binary-long unsigned.
01 expanded binary-long unsigned.
01 next-depth binary-long unsigned.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 name-id binary-long unsigned.
01 d binary-long unsigned.
01 index-val binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'names.cpy'.
copy 'declarations.cpy'.
01 struct-expr binary-long unsigned.
01 field-index binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state struct-expr field-index depth-val result-expr.
    move 0 to result-expr
    if verdict not = 0 goback end-if
    move struct-expr to normalized
    set address of expr-arena to expr-ptr
    if expr-kind(normalized) = 9
        move depth-val to next-depth
        add 1 to next-depth
        call 'string-constructor' using kernel-state normalized expanded
        call 'weak-head' using kernel-state expanded next-depth normalized
    end-if
    call 'expr-spine' using kernel-state normalized head-id args
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(head-id) not = 2 goback end-if
    move expr-a(head-id) to name-id
    set address of name-arena to name-ptr move name-env(name-id) to d
    if d = 0 goback end-if
    set address of decl-arena to decl-ptr
    if decl-kind(d) not = 5 goback end-if
    compute index-val = decl-num-params(d) + field-index
    if index-val < field-index goback end-if
    call 'list-nth' using kernel-state args index-val result-expr
    goback.
end program reduce-projection-core.

identification division.
program-id. infer-projection recursive.
data division.
local-storage section.
01 struct-expr binary-long unsigned.
01 type-name binary-long unsigned.
01 field-index binary-long unsigned.
01 ty binary-long unsigned.
01 struct-type binary-long unsigned.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 p binary-long unsigned.
01 levels binary-long unsigned.
01 params binary-long unsigned.
01 d binary-long unsigned.
01 ctors binary-long unsigned.
01 ctor-name binary-long unsigned.
01 ctor-id binary-long unsigned.
01 ctor-type binary-long unsigned.
01 current-id binary-long unsigned.
01 normalized binary-long unsigned.
01 domain-id binary-long unsigned.
01 body-id binary-long unsigned.
01 arg-id binary-long unsigned.
01 proj-id binary-long unsigned.
01 i binary-long unsigned.
01 nargs binary-long unsigned.
01 nparams binary-long unsigned.
01 nindices binary-long unsigned.
01 universe-id binary-long unsigned.
01 next-depth binary-long unsigned.
01 maybe-prop binary-char unsigned.
01 zero-val binary-long unsigned.
01 proj-kind binary-long unsigned value 7.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'names.cpy'.
copy 'declarations.cpy'.
copy 'levels.cpy'.
copy 'list.cpy'.
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
    move expr-a(input-expr) to type-name move expr-b(input-expr) to field-index
    move expr-c(input-expr) to struct-expr
    call 'infer-type-impl' using kernel-state struct-expr next-depth ty
    call 'weak-head' using kernel-state ty next-depth struct-type
    call 'expr-spine' using kernel-state struct-type head-id args
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(head-id) not = 2 move 1 to verdict goback end-if
    if expr-a(head-id) not = type-name move 1 to verdict goback end-if
    move expr-b(head-id) to levels
    set address of name-arena to name-ptr move name-env(type-name) to d
    if d = 0 move 1 to verdict goback end-if
    set address of decl-arena to decl-ptr
    if decl-kind(d) not = 4 move 1 to verdict goback end-if
    move decl-ctors(d) to ctors move decl-num-params(d) to nparams move decl-num-indices(d) to nindices
    if ctors = 0 move 1 to verdict goback end-if
    set address of list-arena to list-ptr
    if list-length(ctors) not = 1 move 1 to verdict goback end-if
    move list-a(ctors) to ctor-name
    if args not = 0 move list-length(args) to nargs end-if
    if nargs not = nparams + nindices move 1 to verdict goback end-if
    set address of name-arena to name-ptr move name-env(ctor-name) to ctor-id
    set address of decl-arena to decl-ptr
    move decl-type(ctor-id) to ctor-type move decl-params(ctor-id) to params
    call 'instantiate-constant-type' using kernel-state ctor-type params levels current-id
    move args to p
    perform nparams times
        call 'weak-head' using kernel-state current-id next-depth normalized
        if verdict not = 0 goback end-if
        set address of expr-arena to expr-ptr
        if expr-kind(normalized) not = 5 move 1 to verdict goback end-if
        move expr-b(normalized) to body-id
        set address of list-arena to list-ptr move list-a(p) to arg-id move list-b(p) to p
        call 'expr-instantiate1' using kernel-state body-id arg-id current-id
    end-perform
    call 'type-sort-level' using kernel-state struct-type next-depth universe-id
    if verdict not = 0 goback end-if
    set address of level-arena to level-ptr
    if level-never-zero(universe-id) = 0 move 1 to maybe-prop end-if
    perform varying i from 0 by 1 until i > field-index or verdict not = 0
        call 'weak-head' using kernel-state current-id next-depth normalized
        if verdict not = 0 goback end-if
        set address of expr-arena to expr-ptr
        if expr-kind(normalized) not = 5 move 1 to verdict goback end-if
        move expr-a(normalized) to domain-id move expr-b(normalized) to body-id
        if i = field-index
            if maybe-prop = 1 perform check-prop end-if
            move domain-id to result-type goback
        end-if
        if expr-lbvr(body-id) not = 0
            if maybe-prop = 1 perform check-prop end-if
            call 'expr-intern' using kernel-state proj-kind type-name i struct-expr zero-val proj-id
            call 'expr-instantiate1' using kernel-state body-id proj-id current-id
        else move body-id to current-id end-if
    end-perform
    goback.
check-prop.
    call 'type-sort-level' using kernel-state domain-id next-depth universe-id
    if verdict not = 0 exit paragraph end-if
    set address of level-arena to level-ptr
    if level-always-zero(universe-id) = 0 move 1 to verdict end-if.
end program infer-projection.

identification division.
program-id. ind-to-ctor-struct recursive.
data division.
local-storage section.
01 parent-id binary-long unsigned.
01 ctor-id binary-long unsigned.
01 ctor-name binary-long unsigned.
01 name-id binary-long unsigned.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 ty binary-long unsigned.
01 normalized binary-long unsigned.
01 level-id binary-long unsigned.
01 levels binary-long unsigned.
01 ctors binary-long unsigned.
01 nparams binary-long unsigned.
01 nfields binary-long unsigned.
01 chosen binary-long unsigned.
01 current-id binary-long unsigned.
01 proj-id binary-long unsigned.
01 tmp binary-long unsigned.
01 i binary-long unsigned.
01 zero-val binary-long unsigned.
01 const-kind binary-long unsigned value 2.
01 app-kind binary-long unsigned value 3.
01 proj-kind binary-long unsigned value 7.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'names.cpy'.
copy 'declarations.cpy'.
copy 'levels.cpy'.
copy 'list.cpy'.
01 parent-name binary-long unsigned.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state parent-name input-expr depth-val result-expr.
    move input-expr to result-expr
    call 'nonrec-structure' using kernel-state parent-name parent-id
    if parent-id = 0 or verdict not = 0 goback end-if
    call 'expr-spine' using kernel-state input-expr head-id args
    set address of expr-arena to expr-ptr
    if expr-kind(head-id) = 2
        move expr-a(head-id) to name-id
        set address of name-arena to name-ptr move name-env(name-id) to ctor-id
        if ctor-id not = 0
            set address of decl-arena to decl-ptr
            if decl-kind(ctor-id) = 5 goback end-if
        end-if
    end-if
    call 'infer-only' using kernel-state input-expr depth-val ty
    call 'weak-head' using kernel-state ty depth-val normalized
    call 'expr-spine' using kernel-state normalized head-id args
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(head-id) not = 2 goback end-if
    if expr-a(head-id) not = parent-name goback end-if
    move expr-b(head-id) to levels
    call 'type-sort-level' using kernel-state normalized depth-val level-id
    if verdict not = 0 goback end-if
    set address of level-arena to level-ptr
    if level-never-zero(level-id) = 0 goback end-if
    set address of decl-arena to decl-ptr move decl-ctors(parent-id) to ctors
    set address of list-arena to list-ptr move list-a(ctors) to ctor-name
    set address of name-arena to name-ptr move name-env(ctor-name) to ctor-id
    set address of decl-arena to decl-ptr
    move decl-num-params(ctor-id) to nparams move decl-num-fields(ctor-id) to nfields
    call 'expr-intern' using kernel-state const-kind ctor-name levels zero-val zero-val current-id
    call 'list-slice' using kernel-state args zero-val nparams chosen
    call 'expr-app-list' using kernel-state current-id chosen tmp move tmp to current-id
    perform varying i from 0 by 1 until i >= nfields or verdict not = 0
        call 'expr-intern' using kernel-state proj-kind parent-name i input-expr zero-val proj-id
        call 'expr-intern' using kernel-state app-kind current-id proj-id zero-val zero-val tmp
        move tmp to current-id
    end-perform
    move current-id to result-expr
    goback.
end program ind-to-ctor-struct.

identification division.
program-id. def-struct-core recursive.
data division.
local-storage section.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 name-id binary-long unsigned.
01 ctor-id binary-long unsigned.
01 parent-name binary-long unsigned.
01 parent-id binary-long unsigned.
01 nparams binary-long unsigned.
01 nfields binary-long unsigned.
01 i binary-long unsigned.
01 arg-index binary-long unsigned.
01 field-arg binary-long unsigned.
01 proj-id binary-long unsigned.
01 left-type binary-long unsigned.
01 right-type binary-long unsigned.
01 zero-val binary-long unsigned.
01 proj-kind binary-long unsigned value 7.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'names.cpy'.
copy 'declarations.cpy'.
copy 'list.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 depth-val binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs depth-val answer.
    move 0 to answer
    call 'expr-spine' using kernel-state rhs head-id args
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(head-id) not = 2 goback end-if
    move expr-a(head-id) to name-id
    set address of name-arena to name-ptr move name-env(name-id) to ctor-id
    if ctor-id = 0 goback end-if
    set address of decl-arena to decl-ptr
    if decl-kind(ctor-id) not = 5 goback end-if
    move decl-induct(ctor-id) to parent-name
    move decl-num-params(ctor-id) to nparams move decl-num-fields(ctor-id) to nfields
    call 'nonrec-structure' using kernel-state parent-name parent-id
    if parent-id = 0 goback end-if
    move 0 to arg-index
    if args not = 0 set address of list-arena to list-ptr move list-length(args) to arg-index end-if
    if arg-index not = nparams + nfields goback end-if
    call 'infer-only' using kernel-state lhs depth-val left-type
    call 'infer-only' using kernel-state rhs depth-val right-type
    call 'def-equal' using kernel-state left-type right-type depth-val answer
    perform varying i from 0 by 1 until i >= nfields or answer = 0 or verdict not = 0
        move nparams to arg-index
        add i to arg-index
        call 'list-nth' using kernel-state args arg-index field-arg
        call 'expr-intern' using kernel-state proj-kind parent-name i lhs zero-val proj-id
        call 'def-equal' using kernel-state proj-id field-arg depth-val answer
    end-perform
    goback.
end program def-struct-core.

identification division.
program-id. def-unit recursive.
data division.
local-storage section.
01 ty binary-long unsigned.
01 left-type binary-long unsigned.
01 right-type binary-long unsigned.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 name-id binary-long unsigned.
01 parent-id binary-long unsigned.
01 ctor-id binary-long unsigned.
01 ctors binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'names.cpy'.
copy 'declarations.cpy'.
copy 'list.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 depth-val binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs depth-val answer.
    move 0 to answer
    call 'infer-only' using kernel-state lhs depth-val ty
    call 'weak-head' using kernel-state ty depth-val left-type
    call 'expr-spine' using kernel-state left-type head-id args
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(head-id) not = 2 goback end-if
    move expr-a(head-id) to name-id
    call 'nonrec-structure' using kernel-state name-id parent-id
    if parent-id = 0 goback end-if
    set address of decl-arena to decl-ptr move decl-ctors(parent-id) to ctors
    set address of list-arena to list-ptr move list-a(ctors) to name-id
    set address of name-arena to name-ptr move name-env(name-id) to ctor-id
    set address of decl-arena to decl-ptr
    if decl-num-fields(ctor-id) not = 0 goback end-if
    call 'infer-only' using kernel-state rhs depth-val right-type
    call 'def-equal-core' using kernel-state left-type right-type depth-val answer
    goback.
end program def-unit.

*> TypeChecker.lazyDeltaProjReduction compares projected fields after lazy
*> unfolding stalls. A stuck projection retains its original structure in
*> whnfCore, so ordinary application congruence cannot replace this rule.
identification division.
program-id. lazy-delta-projection recursive.
data division.
local-storage section.
01 left-id binary-long unsigned.
01 right-id binary-long unsigned.
01 left-normal binary-long unsigned.
01 right-normal binary-long unsigned.
01 left-field binary-long unsigned.
01 right-field binary-long unsigned.
01 loops binary-long unsigned.
01 next-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 field-index binary-long unsigned.
01 depth-val binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs field-index depth-val answer.
    move 0 to answer
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    move lhs to left-id move rhs to right-id
    perform until verdict not = 0
        if loops >= fuel-lazy-delta move 2 to verdict goback end-if
        add 1 to loops
        call 'lazy-delta-step' using kernel-state left-id right-id next-depth left-normal right-normal answer
        if verdict not = 0 or answer = 1 goback end-if
        move left-normal to left-id move right-normal to right-id
        if answer not = 3 exit perform end-if
    end-perform
    call 'reduce-projection-core' using kernel-state left-id field-index next-depth left-field
    if left-field not = 0
        call 'reduce-projection-core' using kernel-state right-id field-index next-depth right-field
        if right-field not = 0
            call 'def-equal-core' using kernel-state left-field right-field next-depth answer
            goback
        end-if
    end-if
    call 'def-equal-core' using kernel-state left-id right-id next-depth answer
    goback.
end program lazy-delta-projection.

identification division.
program-id. try-unfold-projection-app recursive.
data division.
local-storage section.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 normalized binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-expr.
    move 0 to result-expr
    if verdict not = 0 goback end-if
    call 'expr-spine' using kernel-state input-expr head-id args
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(head-id) not = 7 goback end-if
    call 'weak-head-core' using kernel-state input-expr depth-val normalized
    if normalized not = input-expr move normalized to result-expr end-if
    goback.
end program try-unfold-projection-app.
