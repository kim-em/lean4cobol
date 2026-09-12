*> ElimNestedInductive.run: lower constructor occurrences to a mutual block.
identification division.
program-id. nested-lower.
data division.
local-storage section.
copy 'nested-callback.cpy'.
01 callback-ptr usage pointer.
01 i binary-long unsigned.
01 d binary-long unsigned.
01 cloned binary-long unsigned.
01 n binary-long unsigned.
01 p binary-long unsigned.
01 ty binary-long unsigned.
01 body-id binary-long unsigned.
01 lowered binary-long unsigned.
01 tmp binary-long unsigned.
01 pi-kind binary-long unsigned value 5.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
copy 'list.cpy'.
01 depth-val binary-long unsigned.
procedure division using kernel-state ind-state depth-val.
    if verdict not = 0 goback end-if
    move ind-count to ind-original-count move ind-all to ind-original-all
    move 1 to ind-nested-next
    set nested-ind-pointer to address of ind-state set callback-ptr to address of nested-callback-state
    move depth-val to nested-depth
    set address of ind-arena to ind-ptr move ind-source(1) to d
    set address of decl-arena to decl-ptr move decl-type(d) to ty
    call 'nested-open-params' using kernel-state ty ind-nparams ind-nested-params body-id
    *> Clone parser inputs so lowering never changes exported metadata.
    perform varying i from 1 by 1 until i > ind-original-count or verdict not = 0
        set address of ind-arena to ind-ptr move ind-source(i) to d move ind-ctors(i) to p
        call 'declaration-clone' using kernel-state d cloned
        call 'nested-bind-source' using kernel-state ind-state cloned
        set address of ind-arena to ind-ptr move cloned to ind-source(i)
        perform until p = 0 or verdict not = 0
            set address of list-arena to list-ptr move list-a(p) to n move list-b(p) to p
            set address of name-arena to name-ptr move name-decl(n) to d
            call 'declaration-clone' using kernel-state d cloned
            call 'nested-bind-source' using kernel-state ind-state cloned
        end-perform
    end-perform
    *> New auxiliary types extend ind-count while their constructors are visited.
    perform varying i from 1 by 1 until i > ind-count or verdict not = 0
        if i >= fuel-inductive move 2 to verdict exit perform end-if
        set address of ind-arena to ind-ptr move ind-ctors(i) to p
        perform until p = 0 or verdict not = 0
            set address of list-arena to list-ptr move list-a(p) to n move list-b(p) to p
            set address of name-arena to name-ptr move name-decl(n) to d
            set address of decl-arena to decl-ptr move decl-type(d) to ty
            call 'nested-open-params' using kernel-state ty ind-nparams nested-arguments body-id
            call 'expr-replace' using kernel-state body-id 'nested-lower-occurrence' callback-ptr lowered
            call 'expr-bind-list' using kernel-state pi-kind nested-arguments lowered tmp
            set address of decl-arena to decl-ptr move tmp to decl-type(d)
        end-perform
    end-perform
    goback.
end program nested-lower.

identification division.
program-id. nested-lower-occurrence.
data division.
local-storage section.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 params binary-long unsigned.
01 tail-args binary-long unsigned.
01 name-id binary-long unsigned.
01 d binary-long unsigned.
01 nparams binary-long unsigned.
01 levels binary-long unsigned.
01 applied binary-long unsigned.
01 canonical binary-long unsigned.
01 aux-name binary-long unsigned.
01 fn binary-long unsigned.
01 tmp binary-long unsigned.
01 p binary-long unsigned.
01 field-expr binary-long unsigned.
01 i binary-long unsigned.
01 is-nested binary-char unsigned.
01 loose binary-char unsigned.
01 answer binary-char unsigned.
01 zero-val binary-long unsigned.
01 all-val binary-long unsigned value 4294967295.
01 const-kind binary-long unsigned value 2.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'nested-arena.cpy'.
copy 'nested-callback.cpy'.
copy 'expr.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
copy 'list.cpy'.
01 callback-ptr usage pointer.
01 input-expr binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state callback-ptr input-expr result-expr.
    move 0 to result-expr
    if verdict not = 0 goback end-if
    set address of nested-callback-state to callback-ptr set address of ind-state to nested-ind-pointer
    set address of expr-arena to expr-ptr
    if expr-kind(input-expr) not = 3 goback end-if
    call 'expr-spine' using kernel-state input-expr head-id args
    set address of expr-arena to expr-ptr
    if expr-kind(head-id) not = 2 goback end-if
    move expr-a(head-id) to name-id move expr-b(head-id) to levels
    set address of name-arena to name-ptr move name-env(name-id) to d
    if d = 0 goback end-if
    set address of decl-arena to decl-ptr
    if decl-kind(d) not = 4 goback end-if
    move decl-num-params(d) to nparams
    set address of list-arena to list-ptr
    if list-length(args) < nparams goback end-if
    call 'list-slice' using kernel-state args zero-val nparams params
    move params to p
    perform until p = 0 or verdict not = 0
        set address of list-arena to list-ptr move list-a(p) to field-expr move list-b(p) to p
        set address of expr-arena to expr-ptr
        if expr-lbvr(field-expr) not = 0 move 1 to loose end-if
        call 'ind-has-occ' using kernel-state ind-state field-expr nested-depth answer
        if answer = 1 move 1 to is-nested end-if
    end-perform
    if is-nested = 0 or verdict not = 0 goback end-if
    if loose = 1 move 1 to verdict goback end-if
    call 'expr-app-list' using kernel-state head-id params applied
    call 'expr-remap-locals' using kernel-state applied nested-arguments ind-nested-params canonical
    perform varying i from 1 by 1 until i > ind-nested-count or verdict not = 0
        set address of nested-arena to ind-nested-ptr
        if nested-expr(i) = canonical move nested-name(i) to aux-name exit perform end-if
    end-perform
    if aux-name = 0
        call 'nested-create-family' using kernel-state ind-state d levels params nested-arguments name-id aux-name
    end-if
    if verdict not = 0 goback end-if
    call 'expr-intern' using kernel-state const-kind aux-name ind-levels zero-val zero-val fn
    call 'expr-app-list' using kernel-state fn nested-arguments tmp
    call 'list-slice' using kernel-state args nparams all-val tail-args
    call 'expr-app-list' using kernel-state tmp tail-args result-expr
    goback.
end program nested-lower-occurrence.

identification division.
program-id. nested-create-family.
data division.
local-storage section.
01 family binary-long unsigned.
01 p binary-long unsigned.
01 j-name binary-long unsigned.
01 j-id binary-long unsigned.
01 nparams binary-long unsigned.
01 lparams binary-long unsigned.
01 ty binary-long unsigned.
01 applied binary-long unsigned.
01 canonical binary-long unsigned.
01 aux-name binary-long unsigned.
01 prefixed binary-long unsigned.
01 prefix-id binary-long unsigned.
01 aux-id binary-long unsigned.
01 ctor-id binary-long unsigned.
01 ctor-name binary-long unsigned.
01 new-ctor binary-long unsigned.
01 new-ctor-name binary-long unsigned.
01 ctor-names binary-long unsigned.
01 j-ctors binary-long unsigned.
01 fn binary-long unsigned.
01 tmp binary-long unsigned.
01 tmp2 binary-long unsigned.
01 wanted binary-long unsigned.
01 width binary-long unsigned.
01 index-val binary-long unsigned.
01 zero-val binary-long unsigned.
01 anonymous-name binary-long unsigned value 1.
01 const-kind binary-long unsigned value 2.
01 pi-kind binary-long unsigned value 5.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'nested-arena.cpy'.
copy 'names.cpy'.
copy 'declarations.cpy'.
copy 'list.cpy'.
01 original-id binary-long unsigned.
01 levels binary-long unsigned.
01 params binary-long unsigned.
01 arguments binary-long unsigned.
01 requested-name binary-long unsigned.
01 result-name binary-long unsigned.
procedure division using kernel-state ind-state original-id levels params arguments requested-name result-name.
    move 0 to result-name
    if verdict not = 0 goback end-if
    set address of decl-arena to decl-ptr move decl-all(original-id) to family
    move decl-num-params(original-id) to nparams
    call 'builtin-name' using kernel-state '_nested' prefix-id
    perform until family = 0 or verdict not = 0
        set address of list-arena to list-ptr move list-a(family) to j-name move list-b(family) to family
        set address of name-arena to name-ptr move name-env(j-name) to j-id
        if j-id = 0 move 1 to verdict goback end-if
        set address of decl-arena to decl-ptr
        if decl-kind(j-id) not = 4 move 1 to verdict goback end-if
        move decl-type(j-id) to ty move decl-params(j-id) to lparams move decl-ctors(j-id) to j-ctors
        call 'name-reprefix' using kernel-state j-name anonymous-name prefix-id prefixed
        perform until verdict not = 0
            call 'name-index-after' using kernel-state prefixed ind-nested-next aux-name
            add 1 to ind-nested-next
            set address of name-arena to name-ptr
            if name-env(aux-name) = 0 exit perform end-if
        end-perform
        call 'expr-intern' using kernel-state const-kind j-name levels zero-val zero-val fn
        call 'expr-app-list' using kernel-state fn params applied
        call 'expr-remap-locals' using kernel-state applied arguments ind-nested-params canonical
        call 'instantiate-constant-type' using kernel-state ty lparams levels tmp
        call 'nested-apply-params' using kernel-state tmp nparams params tmp2
        call 'expr-bind-list' using kernel-state pi-kind arguments tmp2 ty
        call 'declaration-clone' using kernel-state j-id aux-id
        if verdict not = 0 goback end-if
        set address of decl-arena to decl-ptr
        move aux-name to decl-name(aux-id) move ty to decl-type(aux-id)
        move ind-lparams to decl-params(aux-id) move ind-nparams to decl-num-params(aux-id)
        call 'nested-bind-source' using kernel-state ind-state aux-id
        compute wanted = ind-count + 1 move length of ind-node to width
        call 'arena-reserve' using ind-ptr ind-cap wanted width verdict
        if verdict not = 0 goback end-if
        add 1 to ind-count move ind-count to index-val
        set address of ind-arena to ind-ptr move aux-id to ind-source(index-val)
        call 'expr-intern' using kernel-state const-kind aux-name ind-levels zero-val zero-val fn
        set address of ind-arena to ind-ptr move fn to ind-constant(index-val)
        call 'list-intern' using kernel-state aux-name zero-val tmp
        call 'list-append' using kernel-state ind-all tmp tmp2 move tmp2 to ind-all
        compute wanted = ind-nested-count + 1 move length of nested-node to width
        call 'arena-reserve' using ind-nested-ptr ind-nested-cap wanted width verdict
        if verdict not = 0 goback end-if
        add 1 to ind-nested-count set address of nested-arena to ind-nested-ptr
        move aux-name to nested-name(ind-nested-count)
        move canonical to nested-expr(ind-nested-count) move index-val to nested-index(ind-nested-count)
        if j-name = requested-name move aux-name to result-name end-if
        move 0 to ctor-names
        move j-ctors to p
        perform until p = 0 or verdict not = 0
            set address of list-arena to list-ptr move list-a(p) to ctor-name move list-b(p) to p
            set address of name-arena to name-ptr move name-env(ctor-name) to ctor-id
            if ctor-id = 0 move 1 to verdict exit perform end-if
            set address of decl-arena to decl-ptr move decl-type(ctor-id) to ty move decl-params(ctor-id) to lparams
            call 'name-reprefix' using kernel-state ctor-name j-name aux-name new-ctor-name
            call 'instantiate-constant-type' using kernel-state ty lparams levels tmp
            call 'nested-apply-params' using kernel-state tmp nparams params tmp2
            call 'expr-bind-list' using kernel-state pi-kind arguments tmp2 ty
            call 'declaration-clone' using kernel-state ctor-id new-ctor
            if verdict not = 0 exit perform end-if
            set address of decl-arena to decl-ptr
            move new-ctor-name to decl-name(new-ctor) move ty to decl-type(new-ctor)
            move ind-lparams to decl-params(new-ctor)
            call 'nested-bind-source' using kernel-state ind-state new-ctor
            call 'list-intern' using kernel-state new-ctor-name ctor-names tmp move tmp to ctor-names
        end-perform
        call 'list-reverse' using kernel-state ctor-names tmp
        set address of ind-arena to ind-ptr move tmp to ind-ctors(index-val)
        set address of decl-arena to decl-ptr move tmp to decl-ctors(aux-id)
    end-perform
    goback.
end program nested-create-family.
