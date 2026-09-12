*> Restore nested applications and public recursor names after mutual checking.
identification division.
program-id. nested-restore-expr.
data division.
local-storage section.
copy 'nested-callback.cpy'.
01 callback-ptr usage pointer.
01 body-id binary-long unsigned.
01 restored binary-long unsigned.
01 binding-kind binary-long unsigned value 4.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
01 rename-recs binary-char unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state ind-state input-expr rename-recs depth-val result-expr.
    move input-expr to result-expr
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(input-expr) = 5 move 5 to binding-kind end-if
    set nested-ind-pointer to address of ind-state set callback-ptr to address of nested-callback-state
    move rename-recs to nested-rec-map move depth-val to nested-depth
    call 'nested-open-params' using kernel-state input-expr ind-nparams nested-arguments body-id
    call 'expr-replace' using kernel-state body-id 'nested-restore-occurrence' callback-ptr restored
    call 'expr-bind-list' using kernel-state binding-kind nested-arguments restored result-expr
    goback.
end program nested-restore-expr.

identification division.
program-id. nested-restore-occurrence.
data division.
local-storage section.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 n binary-long unsigned.
01 levels binary-long unsigned.
01 i binary-long unsigned.
01 d binary-long unsigned.
01 parent-name binary-long unsigned.
01 aux-name binary-long unsigned.
01 nested-value binary-long unsigned.
01 restored binary-long unsigned.
01 original-head binary-long unsigned.
01 original-args binary-long unsigned.
01 original-name binary-long unsigned.
01 new-name binary-long unsigned.
01 new-fn binary-long unsigned.
01 tmp binary-long unsigned.
01 rest binary-long unsigned.
01 ctor-flag binary-char unsigned.
01 zero-val binary-long unsigned.
01 all-val binary-long unsigned value 4294967295.
01 const-kind binary-long unsigned value 2.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
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
    if nested-rec-map = 1 and expr-kind(input-expr) = 2
        move expr-a(input-expr) to n move expr-b(input-expr) to levels
        set address of nested-arena to ind-nested-ptr
        perform varying i from 1 by 1 until i > ind-nested-count
            if nested-old-rec(i) = n
                move nested-new-rec(i) to new-name
                call 'expr-intern' using kernel-state const-kind new-name levels zero-val zero-val result-expr
                goback
            end-if
        end-perform
    end-if
    call 'expr-spine' using kernel-state input-expr head-id args
    set address of expr-arena to expr-ptr
    if expr-kind(head-id) not = 2 goback end-if
    move expr-a(head-id) to n
    set address of nested-arena to ind-nested-ptr
    perform varying i from 1 by 1 until i > ind-nested-count
        if nested-name(i) = n move nested-expr(i) to nested-value exit perform end-if
    end-perform
    if nested-value = 0
        set address of name-arena to name-ptr move name-env(n) to d
        if d = 0 goback end-if
        set address of decl-arena to decl-ptr
        if decl-kind(d) not = 5 goback end-if
        move decl-induct(d) to parent-name
        perform varying i from 1 by 1 until i > ind-nested-count
            if nested-name(i) = parent-name
                move nested-name(i) to aux-name move nested-expr(i) to nested-value
                move 1 to ctor-flag exit perform
            end-if
        end-perform
    end-if
    if nested-value = 0 goback end-if
    if ind-nparams > 0
        if args = 0 move 1 to verdict goback end-if
        set address of list-arena to list-ptr
        if list-length(args) < ind-nparams move 1 to verdict goback end-if
    end-if
    call 'expr-remap-locals' using kernel-state nested-value ind-nested-params nested-arguments restored
    if ctor-flag = 1
        call 'expr-spine' using kernel-state restored original-head original-args
        set address of expr-arena to expr-ptr
        move expr-a(original-head) to original-name move expr-b(original-head) to levels
        call 'name-reprefix' using kernel-state n aux-name original-name new-name
        call 'expr-intern' using kernel-state const-kind new-name levels zero-val zero-val new-fn
        call 'expr-app-list' using kernel-state new-fn original-args tmp move tmp to restored
    end-if
    call 'list-slice' using kernel-state args ind-nparams all-val rest
    call 'expr-app-list' using kernel-state restored rest result-expr
    goback.
end program nested-restore-occurrence.

identification division.
program-id. nested-restore.
data division.
local-storage section.
01 i binary-long unsigned.
01 j binary-long unsigned.
01 d binary-long unsigned.
01 cloned binary-long unsigned.
01 n binary-long unsigned.
01 p binary-long unsigned.
01 ty binary-long unsigned.
01 restored binary-long unsigned.
01 tmp binary-long unsigned.
01 root-rec binary-long unsigned.
01 rec-name binary-long unsigned.
01 renamed binary-long unsigned.
01 zero-val binary-long unsigned.
01 no-rename binary-char unsigned.
01 matched binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'nested-arena.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
copy 'list.cpy'.
01 depth-val binary-long unsigned.
procedure division using kernel-state ind-state depth-val.
    if verdict not = 0 goback end-if
    set address of ind-arena to ind-ptr move ind-rec-name(1) to root-rec
    perform varying j from 1 by 1 until j > ind-nested-count or verdict not = 0
        set address of nested-arena to ind-nested-ptr move nested-index(j) to i
        set address of ind-arena to ind-ptr move ind-rec-name(i) to rec-name
        call 'name-index-after' using kernel-state root-rec j renamed
        set address of nested-arena to ind-nested-ptr
        move rec-name to nested-old-rec(j) move renamed to nested-new-rec(j)
    end-perform
    perform varying i from 1 by 1 until i > ind-original-count or verdict not = 0
        set address of ind-arena to ind-ptr move ind-generated(i) to d move ind-generated-ctors(i) to p
        call 'declaration-clone' using kernel-state d cloned
        if verdict not = 0 exit perform end-if
        set address of decl-arena to decl-ptr move ind-original-all to decl-all(cloned)
        perform save-declaration
        perform until p = 0 or verdict not = 0
            set address of list-arena to list-ptr move list-a(p) to d move list-b(p) to p
            set address of decl-arena to decl-ptr move decl-type(d) to ty
            call 'nested-restore-expr' using kernel-state ind-state ty no-rename depth-val restored
            call 'declaration-clone' using kernel-state d cloned
            if verdict not = 0 exit perform end-if
            set address of decl-arena to decl-ptr move restored to decl-type(cloned)
            perform save-declaration
        end-perform
        set address of ind-arena to ind-ptr move ind-rec-name(i) to rec-name
        call 'nested-restore-rec' using kernel-state ind-state rec-name rec-name depth-val
    end-perform
    perform varying j from 1 by 1 until j > ind-nested-count or verdict not = 0
        set address of nested-arena to ind-nested-ptr
        move nested-old-rec(j) to rec-name move nested-new-rec(j) to renamed
        call 'nested-restore-rec' using kernel-state ind-state rec-name renamed depth-val
    end-perform
    if verdict not = 0 goback end-if
    *> Leave the temporary environment intact until all expressions are restored.
    perform varying i from 1 by 1 until i > ind-count
        set address of ind-arena to ind-ptr move ind-generated(i) to d
        move ind-generated-ctors(i) to p move ind-rec-name(i) to n
        set address of name-arena to name-ptr move 0 to name-env(n)
        set address of decl-arena to decl-ptr move decl-name(d) to n move 0 to name-env(n)
        perform until p = 0
            set address of list-arena to list-ptr move list-a(p) to d move list-b(p) to p
            move decl-name(d) to n move 0 to name-env(n)
        end-perform
    end-perform
    call 'list-reverse' using kernel-state ind-restored-decls p
    perform until p = 0 or verdict not = 0
        set address of list-arena to list-ptr move list-a(p) to d move list-b(p) to p
        set address of decl-arena to decl-ptr move decl-name(d) to n
        set address of name-arena to name-ptr
        if name-env(n) not = 0 move 1 to verdict exit perform end-if
        if ind-allow-primitive = 0
            call 'primitive-name' using kernel-state n matched
            if matched = 1 move 1 to verdict exit perform end-if
        end-if
        set address of name-arena to name-ptr move d to name-env(n)
    end-perform
    call 'tc-cache-free' using kernel-state initialize tc-context
    perform varying j from 1 by 1 until j > ind-nested-count or verdict not = 0
        set address of nested-arena to ind-nested-ptr move nested-expr(j) to ty
        call 'infer-type' using kernel-state ty depth-val tmp
    end-perform
    goback.
save-declaration.
    call 'list-intern' using kernel-state cloned ind-restored-decls tmp move tmp to ind-restored-decls.
end program nested-restore.

identification division.
program-id. nested-restore-rec.
data division.
local-storage section.
01 d binary-long unsigned.
01 cloned binary-long unsigned.
01 ty binary-long unsigned.
01 restored binary-long unsigned.
01 rules binary-long unsigned.
01 new-rules binary-long unsigned.
01 rule-id binary-long unsigned.
01 new-rule binary-long unsigned.
01 ctor-name binary-long unsigned.
01 fields binary-long unsigned.
01 rhs-id binary-long unsigned.
01 tmp binary-long unsigned.
01 index-val binary-long unsigned.
01 nested-value binary-long unsigned.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 parent-name binary-long unsigned.
01 new-ctor-name binary-long unsigned.
01 aux-name binary-long unsigned.
01 wanted binary-long unsigned.
01 width binary-long unsigned.
01 rename-flag binary-char unsigned value 1.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'nested-arena.cpy'.
copy 'expr.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
copy 'list.cpy'.
01 old-name binary-long unsigned.
01 new-name binary-long unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state ind-state old-name new-name depth-val.
    if verdict not = 0 goback end-if
    set address of name-arena to name-ptr move name-env(old-name) to d
    if d = 0 move 1 to verdict goback end-if
    set address of decl-arena to decl-ptr move decl-type(d) to ty move decl-rules(d) to rules
    call 'nested-restore-expr' using kernel-state ind-state ty rename-flag depth-val restored
    call 'declaration-clone' using kernel-state d cloned
    if verdict not = 0 goback end-if
    set address of decl-arena to decl-ptr
    move new-name to decl-name(cloned) move restored to decl-type(cloned)
    move ind-original-all to decl-all(cloned)
    if old-name not = new-name
        set address of nested-arena to ind-nested-ptr
        perform varying index-val from 1 by 1 until index-val > ind-nested-count
            if nested-old-rec(index-val) = old-name
                move nested-expr(index-val) to nested-value move nested-name(index-val) to aux-name exit perform
            end-if
        end-perform
        call 'expr-spine' using kernel-state nested-value head-id args
        set address of expr-arena to expr-ptr move expr-a(head-id) to parent-name
        set address of decl-arena to decl-ptr move parent-name to decl-induct(cloned)
    end-if
    perform until rules = 0 or verdict not = 0
        set address of list-arena to list-ptr move list-a(rules) to rule-id move list-b(rules) to rules
        set address of rule-arena to rule-ptr
        move rule-ctor(rule-id) to ctor-name move rule-fields(rule-id) to fields move rule-rhs(rule-id) to rhs-id
        if old-name not = new-name
            call 'name-reprefix' using kernel-state ctor-name aux-name parent-name new-ctor-name
        else move ctor-name to new-ctor-name end-if
        call 'nested-restore-expr' using kernel-state ind-state rhs-id rename-flag depth-val restored
        compute wanted = rule-count + 1 move length of rule-node to width
        call 'arena-reserve' using rule-ptr rule-cap wanted width verdict
        if verdict not = 0 exit perform end-if
        add 1 to rule-count move rule-count to new-rule set address of rule-arena to rule-ptr
        move new-ctor-name to rule-ctor(new-rule) move fields to rule-fields(new-rule) move restored to rule-rhs(new-rule)
        call 'list-intern' using kernel-state new-rule new-rules tmp move tmp to new-rules
    end-perform
    call 'list-reverse' using kernel-state new-rules tmp
    set address of decl-arena to decl-ptr move tmp to decl-rules(cloned)
    call 'list-intern' using kernel-state cloned ind-restored-decls tmp move tmp to ind-restored-decls
    goback.
end program nested-restore-rec.
