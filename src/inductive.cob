*> Port of Lean4Lean/Inductive/Add.lean, validation stages. Parsed records are
*> inputs; the checked inductive entries are derived from types and parameters.
*> Constructor and recursor generation follows these validation stages.
identification division.
program-id. check-inductive recursive.
data division.
local-storage section.
copy 'inductive.cpy'.
01 saved-tc-context.
copy 'tc-context.cpy'.
01 p binary-long unsigned.
01 q binary-long unsigned.
01 d binary-long unsigned.
01 n binary-long unsigned.
01 ctor-id binary-long unsigned.
01 ctor-name binary-long unsigned.
01 ty binary-long unsigned.
01 tmp binary-long unsigned.
01 i binary-long unsigned.
01 wanted binary-long unsigned.
01 width binary-long unsigned.
01 next-depth binary-long unsigned.
01 stamp binary-long unsigned.
01 zero-val binary-long unsigned.
01 param-kind binary-long unsigned value 4.
01 const-kind binary-long unsigned value 2.
linkage section.
copy 'inductive-arena.cpy'.
copy 'state.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
copy 'list.cpy'.
01 declaration-id binary-long unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state declaration-id depth-val.
    if verdict not = 0 goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    set address of decl-arena to decl-ptr
    move decl-all(declaration-id) to ind-all p
    move decl-params(declaration-id) to ind-lparams
    move decl-num-params(declaration-id) to ind-nparams
    if p = 0 move 1 to verdict goback end-if
    perform until p = 0 or verdict not = 0
        set address of list-arena to list-ptr
        move list-a(p) to n move list-b(p) to p
        set address of name-arena to name-ptr
        move name-decl(n) to d
        if d = 0 move 1 to verdict exit perform end-if
        set address of decl-arena to decl-ptr
        if decl-kind(d) not = 4 move 1 to verdict exit perform end-if
        move ind-count to wanted
        add 1 to wanted
        move length of ind-node to width
        call 'arena-reserve' using ind-ptr ind-cap wanted width verdict
        if verdict not = 0 exit perform end-if
        set address of ind-arena to ind-ptr
        add 1 to ind-count
        move d to ind-source(ind-count)
        move decl-ctors(d) to ind-ctors(ind-count)
        *> Remove the mutual block from remaining/pending before constructor dependencies.
        move 2 to decl-replay(d)
    end-perform
    perform varying i from 1 by 1 until i > ind-count or verdict not = 0
        set address of ind-arena to ind-ptr
        move ind-ctors(i) to p
        perform until p = 0 or verdict not = 0
            set address of list-arena to list-ptr
            move list-a(p) to ctor-name move list-b(p) to p
            set address of name-arena to name-ptr
            move name-decl(ctor-name) to ctor-id
            if ctor-id = 0 move 1 to verdict exit perform end-if
            set address of decl-arena to decl-ptr
            *> Replay rebuilds Constructor from name/type regardless of exported kind.
            move decl-type(ctor-id) to ty
            add 1 to replay-stamp move replay-stamp to stamp
            call 'replay-expr' using kernel-state ty next-depth stamp
        end-perform
    end-perform
    move tc-context to saved-tc-context initialize tc-context
    move ind-lparams to p
    perform until p = 0 or verdict not = 0
        set address of list-arena to list-ptr
        move list-a(p) to n move list-b(p) to q
        perform until q = 0
            if list-a(q) = n move 1 to verdict exit perform end-if
            move list-b(q) to q
        end-perform
        move list-b(p) to p
        call 'level-intern' using kernel-state param-kind n zero-val tmp
        call 'list-intern' using kernel-state tmp ind-levels q
        move q to ind-levels
    end-perform
    call 'list-reverse' using kernel-state ind-levels tmp move tmp to ind-levels
    perform varying i from 1 by 1 until i > ind-count or verdict not = 0
        set address of ind-arena to ind-ptr
        move ind-source(i) to d
        set address of decl-arena to decl-ptr
        move decl-name(d) to n
        call 'expr-intern' using kernel-state const-kind n ind-levels zero-val zero-val tmp
        set address of ind-arena to ind-ptr move tmp to ind-constant(i)
    end-perform
    *> ElimNestedInductive.withParams validates syntactic parameter binders
    *> before normalization, including each constructor's parameter prefix.
    perform varying i from 1 by 1 until i > ind-count or verdict not = 0
        set address of ind-arena to ind-ptr
        move ind-source(i) to d move ind-ctors(i) to p
        set address of decl-arena to decl-ptr move decl-type(d) to ty
        if i = 1 call 'ind-raw-params' using kernel-state ty ind-nparams end-if
        perform until p = 0 or verdict not = 0
            set address of list-arena to list-ptr
            move list-a(p) to n move list-b(p) to p
            set address of name-arena to name-ptr move name-decl(n) to d
            set address of decl-arena to decl-ptr move decl-type(d) to ty
            call 'ind-reserved-scan' using kernel-state ty next-depth
            call 'ind-raw-params' using kernel-state ty ind-nparams
        end-perform
    end-perform
    call 'ind-primitive-check' using kernel-state ind-state
    call 'nested-lower' using kernel-state ind-state next-depth
    call 'ind-check-types' using kernel-state ind-state next-depth
    call 'ind-compute-flags' using kernel-state ind-state next-depth
    if verdict = 0
        *> Provisional inductive constants are visible during constructor checking.
        perform varying i from 1 by 1 until i > ind-count or verdict not = 0
            set address of ind-arena to ind-ptr move ind-source(i) to d
            call 'ind-declare-type' using kernel-state ind-state i d
        end-perform
        call 'ind-check-ctors' using kernel-state ind-state next-depth
    end-if
    call 'ind-declare-ctors' using kernel-state ind-state next-depth
    call 'ind-elimination-level' using kernel-state ind-state next-depth
    call 'ind-build-motives' using kernel-state ind-state next-depth
    call 'ind-build-minors' using kernel-state ind-state next-depth
    call 'ind-build-recursors' using kernel-state ind-state next-depth
    if ind-nested-count > 0 call 'nested-restore' using kernel-state ind-state next-depth end-if
    call 'nested-restore-bindings' using kernel-state ind-state
    if verdict = 0 add 1 to checked-count end-if
    call 'tc-cache-free' using kernel-state
    move saved-tc-context to tc-context
    if ind-nested-ptr not = null call 'arena-release' using ind-nested-ptr end-if
    if ind-ptr not = null call 'arena-release' using ind-ptr end-if
    goback.
end program check-inductive.

identification division.
program-id. ind-raw-params.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 i binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
01 nparams binary-long unsigned.
procedure division using kernel-state input-expr nparams.
    if verdict not = 0 goback end-if
    move input-expr to current-id
    set address of expr-arena to expr-ptr
    perform varying i from 0 by 1 until i >= nparams
        if expr-kind(current-id) not = 5 move 1 to verdict goback end-if
        move expr-b(current-id) to current-id
    end-perform
    goback.
end program ind-raw-params.

identification division.
program-id. ind-check-types.
data division.
local-storage section.
01 i binary-long unsigned.
01 d binary-long unsigned.
01 ty binary-long unsigned.
01 current-id binary-long unsigned.
01 domain-id binary-long unsigned.
01 body-id binary-long unsigned.
01 local-id binary-long unsigned.
01 local-ty binary-long unsigned.
01 params binary-long unsigned.
01 count-params binary-long unsigned.
01 count-indices binary-long unsigned.
01 universe-id binary-long unsigned.
01 loops binary-long unsigned.
01 tmp binary-long unsigned.
01 zero-val binary-long unsigned.
01 answer binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'expr.cpy'.
copy 'declarations.cpy'.
copy 'list.cpy'.
01 depth-val binary-long unsigned.
procedure division using kernel-state ind-state depth-val.
    perform varying i from 1 by 1 until i > ind-count or verdict not = 0
        set address of ind-arena to ind-ptr move ind-source(i) to d
        set address of decl-arena to decl-ptr move decl-type(d) to ty
        set address of expr-arena to expr-ptr
        if expr-lbvr(ty) not = 0 or expr-has-fvar(ty) = 1 move 1 to verdict goback end-if
        call 'expr-params-valid' using kernel-state ty ind-lparams depth-val
        call 'infer-type' using kernel-state ty depth-val tmp
        call 'weak-head' using kernel-state ty depth-val current-id
        move 0 to count-params count-indices loops
        move ind-params to params
        perform until verdict not = 0
            if loops >= fuel-inductive move 2 to verdict exit perform end-if
            add 1 to loops
            set address of expr-arena to expr-ptr
            if expr-kind(current-id) not = 5 exit perform end-if
            move expr-a(current-id) to domain-id move expr-b(current-id) to body-id
            if count-params < ind-nparams
                if i = 1
                    call 'ind-local-fresh' using kernel-state domain-id zero-val local-id
                    call 'list-intern' using kernel-state local-id ind-params tmp
                    move tmp to ind-params
                else
                    set address of list-arena to list-ptr
                    move list-a(params) to local-id move list-b(params) to params
                    set address of expr-arena to expr-ptr
                    move expr-a(local-id) to tmp
                    set address of local-arena to local-ptr
                    move local-type(tmp) to local-ty
                    call 'def-equal' using kernel-state domain-id local-ty depth-val answer
                    if answer = 0 move 1 to verdict exit perform end-if
                end-if
                add 1 to count-params
            else
                call 'ind-local-fresh' using kernel-state domain-id zero-val local-id
                add 1 to count-indices
            end-if
            call 'expr-instantiate1' using kernel-state body-id local-id tmp
            call 'weak-head' using kernel-state tmp depth-val current-id
        end-perform
        if verdict not = 0 goback end-if
        if count-params not = ind-nparams move 1 to verdict goback end-if
        set address of expr-arena to expr-ptr
        if expr-kind(current-id) not = 1 move 1 to verdict goback end-if
        move expr-a(current-id) to universe-id
        if i = 1
            move universe-id to ind-universe
            call 'list-reverse' using kernel-state ind-params tmp move tmp to ind-params
        else
            call 'level-native-equal' using kernel-state universe-id ind-universe answer
            if answer = 0 move 1 to verdict goback end-if
        end-if
        set address of ind-arena to ind-ptr move count-indices to ind-nindices(i)
    end-perform
    goback.
end program ind-check-types.

identification division.
program-id. ind-declare-type.
data division.
local-storage section.
01 n binary-long unsigned.
01 wanted binary-long unsigned.
01 width binary-long unsigned.
01 d binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
01 index-val binary-long unsigned.
01 source-id binary-long unsigned.
procedure division using kernel-state ind-state index-val source-id.
    if verdict not = 0 goback end-if
    set address of decl-arena to decl-ptr move decl-name(source-id) to n
    set address of name-arena to name-ptr
    if name-env(n) not = 0 move 1 to verdict goback end-if
    compute wanted = decl-count + 1 move length of decl-node to width
    call 'arena-reserve' using decl-ptr decl-cap wanted width verdict
    if verdict not = 0 goback end-if
    set address of decl-arena to decl-ptr
    add 1 to decl-count move decl-count to d
    move decl-node(source-id) to decl-node(d)
    move ind-lparams to decl-params(d)
    move ind-nparams to decl-num-params(d)
    set address of ind-arena to ind-ptr
    move ind-nindices(index-val) to decl-num-indices(d)
    move ind-all to decl-all(d)
    move ind-is-rec to decl-is-rec(d) move ind-reflexive to decl-reflexive(d)
    move ind-nested-count to decl-num-nested(d)
    move 0 to decl-unsafe(d)
    move 2 to decl-status(d) decl-replay(d)
    move d to name-env(n) ind-generated(index-val)
    goback.
end program ind-declare-type.

identification division.
program-id. ind-has-occ recursive.
data division.
local-storage section.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 body-id binary-long unsigned.
01 i binary-long unsigned.
01 dc binary-long unsigned.
01 next-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'expr.cpy'.
copy 'declarations.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state ind-state input-expr depth-val answer.
    move 0 to answer
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    set address of expr-arena to expr-ptr
    move expr-kind(input-expr) to k
    move expr-a(input-expr) to a move expr-b(input-expr) to b move expr-c(input-expr) to body-id
    evaluate k
      when 2
        set address of ind-arena to ind-ptr set address of decl-arena to decl-ptr
        perform varying i from 1 by 1 until i > ind-count
            move ind-source(i) to dc
            if decl-name(dc) = a move 1 to answer goback end-if
        end-perform
      when 3 when 4 when 5 when 6
        call 'ind-has-occ' using kernel-state ind-state a next-depth answer
        if answer = 0 call 'ind-has-occ' using kernel-state ind-state b next-depth answer end-if
        if answer = 0 and k = 6
            call 'ind-has-occ' using kernel-state ind-state body-id next-depth answer
        end-if
      when 7 call 'ind-has-occ' using kernel-state ind-state body-id next-depth answer
      when 11 call 'ind-has-occ' using kernel-state ind-state a next-depth answer
    end-evaluate
    goback.
end program ind-has-occ.

identification division.
program-id. ind-valid-app.
data division.
local-storage section.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 params binary-long unsigned.
01 arg-id binary-long unsigned.
01 i binary-long unsigned.
01 nargs binary-long unsigned.
01 answer binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'list.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 type-index binary-long unsigned.
procedure division using kernel-state ind-state input-expr depth-val type-index.
    move 0 to type-index
    call 'expr-spine' using kernel-state input-expr head-id args
    if verdict not = 0 goback end-if
    set address of ind-arena to ind-ptr
    perform varying i from 1 by 1 until i > ind-count
        if ind-constant(i) = head-id exit perform end-if
    end-perform
    if i > ind-count goback end-if
    move 0 to nargs
    if args not = 0
        set address of list-arena to list-ptr move list-length(args) to nargs
    end-if
    if nargs not = ind-nparams + ind-nindices(i) goback end-if
    move ind-params to params
    perform until params = 0
        set address of list-arena to list-ptr
        if list-a(args) not = list-a(params) goback end-if
        move list-b(args) to args move list-b(params) to params
    end-perform
    perform until args = 0 or verdict not = 0
        set address of list-arena to list-ptr
        move list-a(args) to arg-id move list-b(args) to args
        call 'ind-has-occ' using kernel-state ind-state arg-id depth-val answer
        if answer = 1 goback end-if
    end-perform
    if verdict = 0 move i to type-index end-if
    goback.
end program ind-valid-app.

identification division.
program-id. ind-positivity.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 domain-id binary-long unsigned.
01 body-id binary-long unsigned.
01 local-id binary-long unsigned.
01 tmp binary-long unsigned.
01 loops binary-long unsigned.
01 zero-val binary-long unsigned.
01 answer binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state ind-state input-expr depth-val.
    move input-expr to current-id
    perform until verdict not = 0
        if loops >= fuel-inductive move 2 to verdict goback end-if
        add 1 to loops
        call 'weak-head' using kernel-state current-id depth-val tmp move tmp to current-id
        call 'ind-has-occ' using kernel-state ind-state current-id depth-val answer
        if answer = 0 or verdict not = 0 goback end-if
        set address of expr-arena to expr-ptr
        if expr-kind(current-id) not = 5
            call 'ind-valid-app' using kernel-state ind-state current-id depth-val tmp
            if tmp = 0 and verdict = 0 move 1 to verdict end-if
            goback
        end-if
        move expr-a(current-id) to domain-id move expr-b(current-id) to body-id
        call 'ind-has-occ' using kernel-state ind-state domain-id depth-val answer
        if answer = 1 move 1 to verdict goback end-if
        call 'ind-local-fresh' using kernel-state domain-id zero-val local-id
        call 'expr-instantiate1' using kernel-state body-id local-id current-id
    end-perform
    goback.
end program ind-positivity.

identification division.
program-id. ind-check-ctors.
data division.
local-storage section.
01 i binary-long unsigned.
01 p binary-long unsigned.
01 q binary-long unsigned.
01 params binary-long unsigned.
01 n binary-long unsigned.
01 d binary-long unsigned.
01 ty binary-long unsigned.
01 current-id binary-long unsigned.
01 domain-id binary-long unsigned.
01 body-id binary-long unsigned.
01 local-id binary-long unsigned.
01 local-ty binary-long unsigned.
01 sort-id binary-long unsigned.
01 tmp binary-long unsigned.
01 loops binary-long unsigned.
01 zero-val binary-long unsigned.
01 ge-mode binary-long unsigned value 1.
01 answer binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'expr.cpy'.
copy 'levels.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
copy 'list.cpy'.
01 depth-val binary-long unsigned.
procedure division using kernel-state ind-state depth-val.
    perform varying i from 1 by 1 until i > ind-count or verdict not = 0
        set address of ind-arena to ind-ptr move ind-ctors(i) to p
        perform until p = 0 or verdict not = 0
            set address of list-arena to list-ptr
            move list-a(p) to n move list-b(p) to q
            perform until q = 0
                if list-a(q) = n move 1 to verdict goback end-if
                move list-b(q) to q
            end-perform
            move list-b(p) to p
            set address of name-arena to name-ptr move name-decl(n) to d
            set address of decl-arena to decl-ptr move decl-type(d) to ty
            set address of expr-arena to expr-ptr
            if expr-lbvr(ty) not = 0 or expr-has-fvar(ty) = 1 move 1 to verdict goback end-if
            call 'expr-params-valid' using kernel-state ty ind-lparams depth-val
            call 'infer-type' using kernel-state ty depth-val tmp
            move ty to current-id move ind-params to params move 0 to loops
            perform until verdict not = 0
                if loops >= fuel-inductive move 2 to verdict goback end-if
                add 1 to loops
                set address of expr-arena to expr-ptr
                if expr-kind(current-id) not = 5 exit perform end-if
                move expr-a(current-id) to domain-id move expr-b(current-id) to body-id
                if params not = 0
                    set address of list-arena to list-ptr
                    move list-a(params) to local-id move list-b(params) to params
                    set address of expr-arena to expr-ptr move expr-a(local-id) to tmp
                    set address of local-arena to local-ptr move local-type(tmp) to local-ty
                    call 'def-equal' using kernel-state domain-id local-ty depth-val answer
                    if answer = 0 move 1 to verdict goback end-if
                else
                    call 'infer-sort' using kernel-state domain-id depth-val sort-id
                    if verdict not = 0 goback end-if
                    set address of level-arena to level-ptr
                    if level-always-zero(ind-universe) = 0
                        call 'level-compare' using kernel-state ind-universe sort-id ge-mode answer
                        if answer = 0 move 1 to verdict goback end-if
                    end-if
                    call 'ind-positivity' using kernel-state ind-state domain-id depth-val
                    call 'ind-local-fresh' using kernel-state domain-id zero-val local-id
                end-if
                call 'expr-instantiate1' using kernel-state body-id local-id current-id
            end-perform
            call 'ind-valid-app' using kernel-state ind-state current-id depth-val tmp
            if verdict = 0 and tmp not = i move 1 to verdict goback end-if
        end-perform
    end-perform
    goback.
end program ind-check-ctors.

identification division.
program-id. ind-compute-flags.
data division.
local-storage section.
01 i binary-long unsigned.
01 p binary-long unsigned.
01 n binary-long unsigned.
01 d binary-long unsigned.
01 current-id binary-long unsigned.
01 domain-id binary-long unsigned.
01 answer binary-char unsigned.
01 is-function binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
copy 'expr.cpy'.
copy 'list.cpy'.
01 depth-val binary-long unsigned.
procedure division using kernel-state ind-state depth-val.
    perform varying i from 1 by 1 until i > ind-count or verdict not = 0
        set address of ind-arena to ind-ptr move ind-ctors(i) to p
        perform until p = 0 or verdict not = 0
            set address of list-arena to list-ptr move list-a(p) to n move list-b(p) to p
            set address of name-arena to name-ptr move name-decl(n) to d
            set address of decl-arena to decl-ptr move decl-type(d) to current-id
            perform until verdict not = 0
                set address of expr-arena to expr-ptr
                if expr-kind(current-id) not = 5 exit perform end-if
                move expr-a(current-id) to domain-id move expr-b(current-id) to current-id
                move 0 to is-function
                if expr-kind(domain-id) = 5 move 1 to is-function end-if
                call 'ind-has-occ' using kernel-state ind-state domain-id depth-val answer
                if answer = 1
                    move 1 to ind-is-rec
                    if is-function = 1 move 1 to ind-reflexive end-if
                end-if
            end-perform
        end-perform
    end-perform
    goback.
end program ind-compute-flags.

identification division.
program-id. ind-reserved-scan recursive.
data division.
local-storage section.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 body-id binary-long unsigned.
01 n binary-long unsigned.
01 next-depth binary-long unsigned.
01 matched binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'names.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state input-expr depth-val.
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    set address of expr-arena to expr-ptr
    move expr-kind(input-expr) to k
    move expr-a(input-expr) to a move expr-b(input-expr) to b move expr-c(input-expr) to body-id
    if k = 2 or k = 7
        move a to n
        perform until n <= 1
            call 'name-matches' using kernel-state n '_nested' matched
            if matched = 1 move 1 to verdict goback end-if
            set address of name-arena to name-ptr move name-pre(n) to n
        end-perform
    end-if
    evaluate k
      when 3 when 4 when 5 when 6
        call 'ind-reserved-scan' using kernel-state a next-depth
        call 'ind-reserved-scan' using kernel-state b next-depth
        if k = 6 call 'ind-reserved-scan' using kernel-state body-id next-depth end-if
      when 7 call 'ind-reserved-scan' using kernel-state body-id next-depth
      when 11 call 'ind-reserved-scan' using kernel-state a next-depth
    end-evaluate
    goback.
end program ind-reserved-scan.
