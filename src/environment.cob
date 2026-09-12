*> Each declaration runs with fresh type-checker state after dependency
*> replay. Restore the caller even on failure.
identification division.
program-id. check-declaration recursive.
data division.
local-storage section.
01 saved-exprs binary-long unsigned.
01 saved-lists binary-long unsigned.
01 saved-locals binary-long unsigned.
01 saved-tc-context.
copy 'tc-context.cpy'.
linkage section.
copy 'state.cpy'.
01 declaration-id binary-long unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state declaration-id depth-val.
    move expr-count to saved-exprs
    move list-count to saved-lists
    move local-count to saved-locals
    move tc-context to saved-tc-context
    initialize tc-context
    call 'check-declaration-core' using kernel-state declaration-id depth-val
    call 'tc-cache-free' using kernel-state
    if verdict = 0
        call 'expr-rewind' using kernel-state saved-exprs
        call 'list-rewind' using kernel-state saved-lists
        move saved-locals to local-count
    end-if
    move saved-tc-context to tc-context
    goback.
end program check-declaration.

*> Validate ordinary declarations in the environment prepared by replay.
*> Reserved definitions first satisfy their primitive shape/equation checks.
identification division.
program-id. check-declaration-core recursive.
data division.
local-storage section.
01 ty binary-long unsigned.
01 val binary-long unsigned.
01 kind-id binary-long unsigned.
01 params binary-long unsigned.
01 p binary-long unsigned.
01 q binary-long unsigned.
01 universe-id binary-long unsigned.
01 inferred binary-long unsigned.
01 next-depth binary-long unsigned.
01 name-id binary-long unsigned.
01 answer binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'declarations.cpy'.
copy 'expr.cpy'.
copy 'levels.cpy'.
copy 'list.cpy'.
copy 'names.cpy'.
01 declaration-id binary-long unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state declaration-id depth-val.
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    set address of decl-arena to decl-ptr
    evaluate decl-status(declaration-id)
      when 1 move 1 to verdict goback
      when 2 when 3 goback
    end-evaluate
    if decl-unsafe(declaration-id) = 1
        move 3 to decl-status(declaration-id) goback
    end-if
    move decl-name(declaration-id) to name-id
    set address of name-arena to name-ptr
    if name-env(name-id) not = 0 move 1 to verdict goback end-if
    call 'check-primitive-ordinary' using kernel-state declaration-id
    if verdict not = 0 goback end-if
    move 1 to decl-status(declaration-id)
    move decl-type(declaration-id) to ty
    move decl-value(declaration-id) to val
    move decl-kind(declaration-id) to kind-id
    move decl-params(declaration-id) to params p
    set address of list-arena to list-ptr
    perform until p = 0
        move list-b(p) to q
        perform until q = 0
            if list-a(p) = list-a(q) move 1 to verdict goback end-if
            move list-b(q) to q
        end-perform
        move list-b(p) to p
    end-perform
    set address of expr-arena to expr-ptr
    if expr-lbvr(ty) not = 0 or expr-has-fvar(ty) = 1
        move 1 to verdict goback
    end-if
    if val not = 0
        if expr-lbvr(val) not = 0 or expr-has-fvar(val) = 1
            move 1 to verdict goback
        end-if
    end-if
    move depth-val to next-depth
    add 1 to next-depth
    call 'expr-params-valid' using kernel-state ty params next-depth
    if val not = 0
        call 'expr-params-valid' using kernel-state val params next-depth
    end-if
    call 'infer-sort' using kernel-state ty next-depth universe-id
    if verdict not = 0 goback end-if
    if kind-id = 2
        set address of level-arena to level-ptr
        if level-always-zero(universe-id) = 0 move 1 to verdict goback end-if
    end-if
    if val not = 0
        call 'infer-type' using kernel-state val next-depth inferred
        call 'def-equal' using kernel-state inferred ty next-depth answer
        if verdict not = 0 goback end-if
        if answer = 0 move 1 to verdict goback end-if
    end-if
    set address of decl-arena to decl-ptr
    move 2 to decl-status(declaration-id)
    set address of name-arena to name-ptr
    move declaration-id to name-env(name-id)
    add 1 to checked-count
    goback.
end program check-declaration-core.

identification division.
program-id. instantiate-constant-type recursive.
data division.
local-storage section.
01 vector-ptr usage pointer.
01 vector-cap binary-long unsigned.
01 vector-count binary-long unsigned.
01 width binary-long unsigned value 8.
01 p binary-long unsigned.
01 u binary-long unsigned.
01 i binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'list.cpy'.
01 input-expr binary-long unsigned.
01 param-list binary-long unsigned.
01 level-list binary-long unsigned.
01 result-expr binary-long unsigned.
01 vector-data based.
   02 vector-entry occurs 1 to 67108864 depending on vector-cap.
      03 vector-name binary-long unsigned.
      03 vector-level binary-long unsigned.
procedure division using kernel-state input-expr param-list level-list result-expr.
    move input-expr to result-expr
    if verdict not = 0 goback end-if
    if param-list = 0 or level-list = 0
        if param-list not = level-list move 1 to verdict end-if
        goback
    end-if
    set address of list-arena to list-ptr
    if list-length(param-list) not = list-length(level-list)
        move 1 to verdict goback
    end-if
    move list-length(param-list) to vector-count
    call 'arena-reserve' using vector-ptr vector-cap vector-count width verdict
    if verdict not = 0 goback end-if
    set address of vector-data to vector-ptr
    move param-list to p move level-list to u
    perform varying i from 1 by 1 until i > vector-count
        move list-a(p) to vector-name(i)
        move list-a(u) to vector-level(i)
        move list-b(p) to p move list-b(u) to u
    end-perform
    call 'expr-level-params' using kernel-state input-expr vector-count vector-ptr result-expr
    call 'arena-release' using vector-ptr
    goback.
end program instantiate-constant-type.

identification division.
program-id. expr-params-valid recursive.
data division.
local-storage section.
01 cache-family binary-long unsigned value 9.
01 cached binary-long unsigned.
01 zero-val binary-long unsigned.
01 one-val binary-long unsigned value 1.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 body-id binary-long unsigned.
01 list-id binary-long unsigned.
01 level-id binary-long unsigned.
01 next-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'list.cpy'.
01 input-expr binary-long unsigned.
01 params binary-long unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state input-expr params depth-val.
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    set address of expr-arena to expr-ptr
    if expr-has-param(input-expr) = 0 goback end-if
    *> Validation depends only on this immutable node and parameter list.
    *> Shared DAG branches must not be revisited as an exponentially large tree.
    call 'tc-cache' using kernel-state cache-family input-expr params zero-val cached
    if cached not = 0 goback end-if
    move expr-kind(input-expr) to k
    move expr-a(input-expr) to a
    move expr-b(input-expr) to b
    move expr-c(input-expr) to body-id
    move depth-val to next-depth
    add 1 to next-depth
    evaluate k
      when 1 call 'level-params-valid' using kernel-state a params next-depth
      when 2
        move b to list-id
        perform until list-id = 0 or verdict not = 0
            set address of list-arena to list-ptr
            move list-a(list-id) to level-id
            move list-b(list-id) to list-id
            call 'level-params-valid' using kernel-state level-id params next-depth
        end-perform
      when 3 when 4 when 5
        call 'expr-params-valid' using kernel-state a params next-depth
        call 'expr-params-valid' using kernel-state b params next-depth
      when 6
        call 'expr-params-valid' using kernel-state a params next-depth
        call 'expr-params-valid' using kernel-state b params next-depth
        call 'expr-params-valid' using kernel-state body-id params next-depth
      when 7 call 'expr-params-valid' using kernel-state body-id params next-depth
      when 11 call 'expr-params-valid' using kernel-state a params next-depth
    end-evaluate
    if verdict = 0
        call 'tc-cache' using kernel-state cache-family input-expr params one-val cached
    end-if
    goback.
end program expr-params-valid.

identification division.
program-id. level-params-valid recursive.
data division.
local-storage section.
01 cache-family binary-long unsigned value 10.
01 cached binary-long unsigned.
01 zero-val binary-long unsigned.
01 one-val binary-long unsigned value 1.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 p binary-long unsigned.
01 next-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'levels.cpy'.
copy 'list.cpy'.
01 input-level binary-long unsigned.
01 params binary-long unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state input-level params depth-val.
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    set address of level-arena to level-ptr
    if level-has-param(input-level) = 0 goback end-if
    *> Validation depends only on this immutable node and parameter list.
    *> Shared DAG branches must not be revisited as an exponentially large tree.
    call 'tc-cache' using kernel-state cache-family input-level params zero-val cached
    if cached not = 0 goback end-if
    move level-kind(input-level) to k
    move level-a(input-level) to a move level-b(input-level) to b
    move depth-val to next-depth
    add 1 to next-depth
    evaluate k
      when 4
        set address of list-arena to list-ptr
        move params to p
        perform until p = 0
            if list-a(p) = a exit perform end-if
            move list-b(p) to p
        end-perform
        if p = 0 move 1 to verdict end-if
      when 1 call 'level-params-valid' using kernel-state a params next-depth
      when 2 when 3
        call 'level-params-valid' using kernel-state a params next-depth
        call 'level-params-valid' using kernel-state b params next-depth
    end-evaluate
    if verdict = 0
        call 'tc-cache' using kernel-state cache-family input-level params one-val cached
    end-if
    goback.
end program level-params-valid.
