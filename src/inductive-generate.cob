*> Canonical declaration generation following Lean4Lean/Inductive/Add.lean.
identification division.
program-id. ind-declare-ctors.
data division.
local-storage section.
01 i binary-long unsigned.
01 p binary-long unsigned.
01 n binary-long unsigned.
01 parent-name binary-long unsigned.
01 src-id binary-long unsigned.
01 gen-id binary-long unsigned.
01 ty binary-long unsigned.
01 current-id binary-long unsigned.
01 domain-id binary-long unsigned.
01 arity binary-long unsigned.
01 cidx binary-long unsigned.
01 wanted binary-long unsigned.
01 width binary-long unsigned.
01 tmp binary-long unsigned.
01 generated-list binary-long unsigned.
01 answer binary-char unsigned.
01 reflexive-arg binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'expr.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
copy 'list.cpy'.
01 depth-val binary-long unsigned.
procedure division using kernel-state ind-state depth-val.
    perform varying i from 1 by 1 until i > ind-count or verdict not = 0
        set address of ind-arena to ind-ptr
        move ind-source(i) to src-id move ind-ctors(i) to p
        set address of decl-arena to decl-ptr move decl-name(src-id) to parent-name
        move 0 to cidx generated-list
        perform until p = 0 or verdict not = 0
            set address of list-arena to list-ptr
            move list-a(p) to n move list-b(p) to p
            set address of name-arena to name-ptr
            if name-env(n) not = 0 move 1 to verdict goback end-if
            move name-decl(n) to src-id
            set address of decl-arena to decl-ptr move decl-type(src-id) to ty current-id
            move 0 to arity
            perform until verdict not = 0
                set address of expr-arena to expr-ptr
                if expr-kind(current-id) not = 5 exit perform end-if
                move expr-a(current-id) to domain-id move expr-b(current-id) to current-id
                move 0 to reflexive-arg
                if expr-kind(domain-id) = 5 move 1 to reflexive-arg end-if
                call 'ind-has-occ' using kernel-state ind-state domain-id depth-val answer
                if answer = 1
                    move 1 to ind-is-rec
                    if reflexive-arg = 1 move 1 to ind-reflexive end-if
                end-if
                add 1 to arity
            end-perform
            if arity < ind-nparams move 1 to verdict goback end-if
            compute wanted = decl-count + 1 move length of decl-node to width
            call 'arena-reserve' using decl-ptr decl-cap wanted width verdict
            if verdict not = 0 goback end-if
            set address of decl-arena to decl-ptr
            add 1 to decl-count move decl-count to gen-id
            move n to decl-name(gen-id) move 5 to decl-kind(gen-id)
            move ind-lparams to decl-params(gen-id) move ty to decl-type(gen-id)
            move parent-name to decl-induct(gen-id) move cidx to decl-cidx(gen-id)
            move ind-nparams to decl-num-params(gen-id)
            compute decl-num-fields(gen-id) = arity - ind-nparams
            move 2 to decl-status(gen-id) decl-replay(gen-id)
            move gen-id to name-env(n)
            call 'list-intern' using kernel-state gen-id generated-list tmp
            move tmp to generated-list add 1 to cidx
        end-perform
        call 'list-reverse' using kernel-state generated-list tmp
        set address of ind-arena to ind-ptr move tmp to ind-generated-ctors(i)
    end-perform
    perform varying i from 1 by 1 until i > ind-count or verdict not = 0
        set address of ind-arena to ind-ptr move ind-generated(i) to gen-id
        set address of decl-arena to decl-ptr
        move ind-is-rec to decl-is-rec(gen-id) move ind-reflexive to decl-reflexive(gen-id)
    end-perform
    goback.
end program ind-declare-ctors.

identification division.
program-id. ind-elimination-level.
data division.
local-storage section.
01 large-elim binary-char unsigned.
01 d binary-long unsigned.
01 ty binary-long unsigned.
01 current-id binary-long unsigned.
01 domain-id binary-long unsigned.
01 body-id binary-long unsigned.
01 local-id binary-long unsigned.
01 sort-id binary-long unsigned.
01 to-check binary-long unsigned.
01 p binary-long unsigned.
01 args binary-long unsigned.
01 q binary-long unsigned.
01 head-id binary-long unsigned.
01 count-args binary-long unsigned.
01 count-ctors binary-long unsigned.
01 loops binary-long unsigned.
01 tmp binary-long unsigned.
01 level-name binary-long unsigned.
01 index-val binary-long unsigned.
01 label-text pic x(32).
01 label-number pic Z(9)9.
01 zero-val binary-long unsigned.
01 param-kind binary-long unsigned value 4.
01 one-val binary-long unsigned value 1.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'expr.cpy'.
copy 'levels.cpy'.
copy 'declarations.cpy'.
copy 'list.cpy'.
01 depth-val binary-long unsigned.
procedure division using kernel-state ind-state depth-val.
    if verdict not = 0 goback end-if
    set address of level-arena to level-ptr
    if level-never-zero(ind-universe) = 1 move 1 to large-elim end-if
    if ind-count = 1
        set address of ind-arena to ind-ptr move ind-generated-ctors(1) to p
        if p = 0
            move 1 to large-elim
        else
            set address of list-arena to list-ptr
            move list-length(p) to count-ctors move list-a(p) to d
            if count-ctors = 1
                set address of decl-arena to decl-ptr move decl-type(d) to current-id ty
                set address of level-arena to level-ptr
                if level-always-zero(ind-universe) = 1 and decl-num-fields(d) = 0 move 1 to ind-k end-if
                if large-elim = 0
                    move 1 to large-elim
                    perform until verdict not = 0
                        if loops >= fuel-inductive move 2 to verdict goback end-if
                        add 1 to loops
                        set address of expr-arena to expr-ptr
                        if expr-kind(current-id) not = 5 exit perform end-if
                        move expr-a(current-id) to domain-id move expr-b(current-id) to body-id
                        call 'ind-local-fresh' using kernel-state domain-id zero-val local-id
                        if count-args >= ind-nparams
                            call 'infer-sort' using kernel-state domain-id depth-val sort-id
                            if verdict not = 0 goback end-if
                            set address of level-arena to level-ptr
                            if level-always-zero(sort-id) = 0
                                call 'list-intern' using kernel-state local-id to-check tmp move tmp to to-check
                            end-if
                        end-if
                        call 'expr-instantiate1' using kernel-state body-id local-id current-id
                        add 1 to count-args
                    end-perform
                    call 'expr-spine' using kernel-state current-id head-id args
                    perform until to-check = 0 or verdict not = 0
                        set address of list-arena to list-ptr
                        move list-a(to-check) to local-id move list-b(to-check) to to-check
                        move args to q
                        perform until q = 0
                            if list-a(q) = local-id exit perform end-if
                            move list-b(q) to q
                        end-perform
                        if q = 0 move 0 to large-elim exit perform end-if
                    end-perform
                end-if
            end-if
        end-if
    end-if
    move 1 to ind-elim-level
    move ind-levels to ind-rec-levels move ind-lparams to ind-rec-lparams
    if large-elim = 0 goback end-if
    move 'u' to label-text
    perform until verdict not = 0
        call 'builtin-name' using kernel-state function trim(label-text) level-name
        move ind-lparams to p
        set address of list-arena to list-ptr
        perform until p = 0
            if list-a(p) = level-name exit perform end-if
            move list-b(p) to p
        end-perform
        if p = 0 exit perform end-if
        add 1 to index-val move index-val to label-number
        move spaces to label-text
        string 'u_' function trim(label-number) into label-text end-string
    end-perform
    call 'level-intern' using kernel-state param-kind level-name zero-val ind-elim-level
    call 'list-intern' using kernel-state ind-elim-level ind-levels ind-rec-levels
    call 'list-intern' using kernel-state level-name ind-lparams ind-rec-lparams
    goback.
end program ind-elimination-level.

identification division.
program-id. ind-build-motives.
data division.
local-storage section.
01 i binary-long unsigned.
01 d binary-long unsigned.
01 ty binary-long unsigned.
01 current-id binary-long unsigned.
01 domain-id binary-long unsigned.
01 body-id binary-long unsigned.
01 indices binary-long unsigned.
01 params binary-long unsigned.
01 local-id binary-long unsigned.
01 major-id binary-long unsigned.
01 motive-id binary-long unsigned.
01 tmp binary-long unsigned.
01 tmp2 binary-long unsigned.
01 fn-id binary-long unsigned.
01 loops binary-long unsigned.
01 zero-val binary-long unsigned.
01 sort-kind binary-long unsigned value 1.
01 pi-kind binary-long unsigned value 5.
01 name-kind binary-long unsigned value 1.
01 text-size binary-long unsigned value 3.
01 name-id binary-long unsigned.
01 rec-name binary-long unsigned.
01 name-num binary-double unsigned.
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
        set address of decl-arena to decl-ptr move decl-type(d) to ty move decl-name(d) to name-id
        call 'name-intern' using kernel-state name-kind name-id name-num 'rec' text-size rec-name
        set address of ind-arena to ind-ptr move rec-name to ind-rec-name(i)
        call 'weak-head' using kernel-state ty depth-val current-id
        move ind-params to params move 0 to indices loops
        perform until verdict not = 0
            if loops >= fuel-inductive move 2 to verdict goback end-if
            add 1 to loops
            set address of expr-arena to expr-ptr
            if expr-kind(current-id) not = 5 exit perform end-if
            move expr-a(current-id) to domain-id move expr-b(current-id) to body-id
            if params not = 0
                set address of list-arena to list-ptr
                move list-a(params) to local-id move list-b(params) to params
            else
                call 'ind-local-fresh' using kernel-state domain-id zero-val local-id
                call 'list-intern' using kernel-state local-id indices tmp move tmp to indices
            end-if
            call 'expr-instantiate1' using kernel-state body-id local-id tmp
            call 'weak-head' using kernel-state tmp depth-val current-id
        end-perform
        call 'list-reverse' using kernel-state indices tmp move tmp to indices
        set address of ind-arena to ind-ptr move ind-constant(i) to fn-id
        call 'expr-app-list' using kernel-state fn-id ind-params tmp
        call 'expr-app-list' using kernel-state tmp indices ty
        call 'ind-local-fresh' using kernel-state ty zero-val major-id
        call 'expr-intern' using kernel-state sort-kind ind-elim-level zero-val zero-val zero-val ty
        call 'list-intern' using kernel-state major-id zero-val tmp2
        call 'expr-bind-list' using kernel-state pi-kind tmp2 ty tmp
        call 'expr-bind-list' using kernel-state pi-kind indices tmp ty
        call 'ind-local-fresh' using kernel-state ty zero-val motive-id
        call 'list-intern' using kernel-state motive-id ind-motives tmp move tmp to ind-motives
        set address of ind-arena to ind-ptr
        move motive-id to ind-motive(i) move major-id to ind-major(i) move indices to ind-indices(i)
    end-perform
    call 'list-reverse' using kernel-state ind-motives tmp move tmp to ind-motives
    goback.
end program ind-build-motives.

*> Decompose a recursive argument type forall xs, I params indices. The
*> returned index is zero when it is not recursive; xs/indices use fvars.
identification division.
program-id. ind-rec-arg.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 domain-id binary-long unsigned.
01 body-id binary-long unsigned.
01 local-id binary-long unsigned.
01 locals-list binary-long unsigned.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 tmp binary-long unsigned.
01 loops binary-long unsigned.
01 i binary-long unsigned.
01 zero-val binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'expr.cpy'.
copy 'list.cpy'.
01 input-type binary-long unsigned.
01 depth-val binary-long unsigned.
01 type-index binary-long unsigned.
01 local-args binary-long unsigned.
01 result-indices binary-long unsigned.
procedure division using kernel-state ind-state input-type depth-val type-index local-args result-indices.
    move 0 to type-index local-args result-indices
    move input-type to current-id
    perform until verdict not = 0
        if loops >= fuel-inductive move 2 to verdict goback end-if
        add 1 to loops
        call 'weak-head' using kernel-state current-id depth-val tmp move tmp to current-id
        if verdict not = 0 goback end-if
        set address of expr-arena to expr-ptr
        if expr-kind(current-id) not = 5 exit perform end-if
        move expr-a(current-id) to domain-id move expr-b(current-id) to body-id
        call 'ind-local-fresh' using kernel-state domain-id zero-val local-id
        call 'list-intern' using kernel-state local-id locals-list tmp move tmp to locals-list
        call 'expr-instantiate1' using kernel-state body-id local-id current-id
    end-perform
    call 'ind-valid-app' using kernel-state ind-state current-id depth-val type-index
    if verdict not = 0 or type-index = 0 goback end-if
    call 'list-reverse' using kernel-state locals-list local-args
    call 'expr-spine' using kernel-state current-id head-id args
    set address of list-arena to list-ptr
    perform ind-nparams times move list-b(args) to args end-perform
    move args to result-indices
    goback.
end program ind-rec-arg.

identification division.
program-id. ind-build-minors.
data division.
local-storage section.
01 i binary-long unsigned.
01 p binary-long unsigned.
01 d binary-long unsigned.
01 name-id binary-long unsigned.
01 ty binary-long unsigned.
01 current-id binary-long unsigned.
01 params binary-long unsigned.
01 fields binary-long unsigned.
01 recargs binary-long unsigned.
01 ihs binary-long unsigned.
01 domain-id binary-long unsigned.
01 body-id binary-long unsigned.
01 local-id binary-long unsigned.
01 target-id binary-long unsigned.
01 xs binary-long unsigned.
01 indices binary-long unsigned.
01 target-motive binary-long unsigned.
01 ctor-app binary-long unsigned.
01 minor-ty binary-long unsigned.
01 minor-id binary-long unsigned.
01 ui binary-long unsigned.
01 ui-app binary-long unsigned.
01 q binary-long unsigned.
01 tmp binary-long unsigned.
01 tmp2 binary-long unsigned.
01 loops binary-long unsigned.
01 zero-val binary-long unsigned.
01 const-kind binary-long unsigned value 2.
01 app-kind binary-long unsigned value 3.
01 pi-kind binary-long unsigned value 5.
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
        set address of ind-arena to ind-ptr move ind-generated-ctors(i) to p
        perform until p = 0 or verdict not = 0
            set address of list-arena to list-ptr
            move list-a(p) to d move list-b(p) to p
            set address of decl-arena to decl-ptr
            move decl-type(d) to current-id move decl-name(d) to name-id
            move ind-params to params move 0 to fields recargs ihs loops
            perform until verdict not = 0
                if loops >= fuel-inductive move 2 to verdict goback end-if
                add 1 to loops
                set address of expr-arena to expr-ptr
                if expr-kind(current-id) not = 5 exit perform end-if
                move expr-a(current-id) to domain-id move expr-b(current-id) to body-id
                if params not = 0
                    set address of list-arena to list-ptr
                    move list-a(params) to local-id move list-b(params) to params
                else
                    call 'ind-local-fresh' using kernel-state domain-id zero-val local-id
                    call 'list-intern' using kernel-state local-id fields tmp move tmp to fields
                    call 'ind-rec-arg' using kernel-state ind-state domain-id depth-val target-id xs indices
                    if target-id not = 0
                        call 'list-intern' using kernel-state local-id recargs tmp move tmp to recargs
                    end-if
                end-if
                call 'expr-instantiate1' using kernel-state body-id local-id current-id
            end-perform
            call 'list-reverse' using kernel-state fields tmp move tmp to fields
            call 'list-reverse' using kernel-state recargs tmp move tmp to recargs
            if verdict not = 0 goback end-if
            set address of decl-arena to decl-ptr
            move fields to decl-gen-fields(d) move recargs to decl-gen-recargs(d)
            move current-id to decl-gen-result(d)
            move recargs to q
            perform until q = 0 or verdict not = 0
                set address of list-arena to list-ptr move list-a(q) to ui move list-b(q) to q
                call 'infer-only' using kernel-state ui depth-val ty
                call 'ind-rec-arg' using kernel-state ind-state ty depth-val target-id xs indices
                if target-id = 0 move 3 to verdict goback end-if
                call 'expr-app-list' using kernel-state ui xs ui-app
                set address of ind-arena to ind-ptr move ind-motive(target-id) to target-motive
                call 'expr-app-list' using kernel-state target-motive indices tmp
                call 'expr-intern' using kernel-state app-kind tmp ui-app zero-val zero-val tmp2
                call 'expr-bind-list' using kernel-state pi-kind xs tmp2 ty
                call 'ind-local-fresh' using kernel-state ty zero-val local-id
                call 'list-intern' using kernel-state local-id ihs tmp move tmp to ihs
            end-perform
            call 'list-reverse' using kernel-state ihs tmp move tmp to ihs
            call 'ind-rec-arg' using kernel-state ind-state current-id depth-val target-id xs indices
            if target-id = 0 move 3 to verdict goback end-if
            call 'expr-intern' using kernel-state const-kind name-id ind-levels zero-val zero-val tmp
            call 'expr-app-list' using kernel-state tmp ind-params tmp2
            call 'expr-app-list' using kernel-state tmp2 fields ctor-app
            set address of ind-arena to ind-ptr move ind-motive(target-id) to target-motive
            call 'expr-app-list' using kernel-state target-motive indices tmp
            call 'expr-intern' using kernel-state app-kind tmp ctor-app zero-val zero-val minor-ty
            call 'expr-bind-list' using kernel-state pi-kind ihs minor-ty tmp
            call 'expr-bind-list' using kernel-state pi-kind fields tmp minor-ty
            call 'ind-local-fresh' using kernel-state minor-ty zero-val minor-id
            call 'list-intern' using kernel-state minor-id ind-minors tmp move tmp to ind-minors
        end-perform
    end-perform
    call 'list-reverse' using kernel-state ind-minors tmp move tmp to ind-minors
    goback.
end program ind-build-minors.

identification division.
program-id. ind-build-recursors.
data division.
local-storage section.
01 i binary-long unsigned.
01 p binary-long unsigned.
01 q binary-long unsigned.
01 d binary-long unsigned.
01 minor-pos binary-long unsigned.
01 minor-id binary-long unsigned.
01 fields binary-long unsigned.
01 recargs binary-long unsigned.
01 ihs binary-long unsigned.
01 ui binary-long unsigned.
01 ty binary-long unsigned.
01 target-id binary-long unsigned.
01 xs binary-long unsigned.
01 indices binary-long unsigned.
01 target-name binary-long unsigned.
01 rec-name binary-long unsigned.
01 ctor-name binary-long unsigned.
01 nfields binary-long unsigned.
01 ui-app binary-long unsigned.
01 current-id binary-long unsigned.
01 tmp binary-long unsigned.
01 tmp2 binary-long unsigned.
01 rhs-id binary-long unsigned.
01 rules binary-long unsigned.
01 rule-id binary-long unsigned.
01 gen-id binary-long unsigned.
01 motive-id binary-long unsigned.
01 major-id binary-long unsigned.
01 wanted binary-long unsigned.
01 width binary-long unsigned.
01 zero-val binary-long unsigned.
01 const-kind binary-long unsigned value 2.
01 app-kind binary-long unsigned value 3.
01 lam-kind binary-long unsigned value 4.
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
    perform varying i from 1 by 1 until i > ind-count or verdict not = 0
        set address of ind-arena to ind-ptr move ind-generated-ctors(i) to p
        move ind-rec-name(i) to rec-name move 0 to rules
        perform until p = 0 or verdict not = 0
            set address of list-arena to list-ptr move list-a(p) to d move list-b(p) to p
            set address of decl-arena to decl-ptr
            move decl-gen-fields(d) to fields move decl-gen-recargs(d) to recargs
            move decl-name(d) to ctor-name move decl-num-fields(d) to nfields
            move recargs to q move 0 to ihs
            perform until q = 0 or verdict not = 0
                set address of list-arena to list-ptr move list-a(q) to ui move list-b(q) to q
                call 'infer-only' using kernel-state ui depth-val ty
                call 'ind-rec-arg' using kernel-state ind-state ty depth-val target-id xs indices
                if target-id = 0 move 3 to verdict goback end-if
                set address of ind-arena to ind-ptr move ind-rec-name(target-id) to target-name
                call 'expr-intern' using kernel-state const-kind target-name ind-rec-levels zero-val zero-val current-id
                call 'expr-app-list' using kernel-state current-id ind-params tmp move tmp to current-id
                call 'expr-app-list' using kernel-state current-id ind-motives tmp move tmp to current-id
                call 'expr-app-list' using kernel-state current-id ind-minors tmp move tmp to current-id
                call 'expr-app-list' using kernel-state current-id indices tmp move tmp to current-id
                call 'expr-app-list' using kernel-state ui xs ui-app
                call 'expr-intern' using kernel-state app-kind current-id ui-app zero-val zero-val tmp
                call 'expr-bind-list' using kernel-state lam-kind xs tmp tmp2
                call 'list-intern' using kernel-state tmp2 ihs tmp move tmp to ihs
            end-perform
            call 'list-reverse' using kernel-state ihs tmp move tmp to ihs
            call 'list-nth' using kernel-state ind-minors minor-pos minor-id
            add 1 to minor-pos
            call 'expr-app-list' using kernel-state minor-id fields tmp
            call 'expr-app-list' using kernel-state tmp ihs current-id
            call 'expr-bind-list' using kernel-state lam-kind fields current-id tmp move tmp to current-id
            call 'expr-bind-list' using kernel-state lam-kind ind-minors current-id tmp move tmp to current-id
            call 'expr-bind-list' using kernel-state lam-kind ind-motives current-id tmp move tmp to current-id
            call 'expr-bind-list' using kernel-state lam-kind ind-params current-id rhs-id
            compute wanted = rule-count + 1 move length of rule-node to width
            call 'arena-reserve' using rule-ptr rule-cap wanted width verdict
            if verdict not = 0 goback end-if
            set address of rule-arena to rule-ptr add 1 to rule-count move rule-count to rule-id
            move ctor-name to rule-ctor(rule-id) move nfields to rule-fields(rule-id) move rhs-id to rule-rhs(rule-id)
            call 'list-intern' using kernel-state rule-id rules tmp move tmp to rules
        end-perform
        call 'list-reverse' using kernel-state rules tmp move tmp to rules
        set address of ind-arena to ind-ptr
        move ind-motive(i) to motive-id move ind-major(i) to major-id move ind-indices(i) to indices
        call 'expr-app-list' using kernel-state motive-id indices tmp
        call 'expr-intern' using kernel-state app-kind tmp major-id zero-val zero-val current-id
        call 'list-intern' using kernel-state major-id zero-val tmp2
        call 'expr-bind-list' using kernel-state pi-kind tmp2 current-id tmp move tmp to current-id
        call 'expr-bind-list' using kernel-state pi-kind indices current-id tmp move tmp to current-id
        call 'expr-bind-list' using kernel-state pi-kind ind-minors current-id tmp move tmp to current-id
        call 'expr-bind-list' using kernel-state pi-kind ind-motives current-id tmp move tmp to current-id
        call 'expr-bind-list' using kernel-state pi-kind ind-params current-id ty
        if verdict not = 0 goback end-if
        set address of name-arena to name-ptr
        if name-env(rec-name) not = 0 move 1 to verdict goback end-if
        compute wanted = decl-count + 1 move length of decl-node to width
        call 'arena-reserve' using decl-ptr decl-cap wanted width verdict
        if verdict not = 0 goback end-if
        set address of decl-arena to decl-ptr add 1 to decl-count move decl-count to gen-id
        move rec-name to decl-name(gen-id) move 6 to decl-kind(gen-id)
        move ind-rec-lparams to decl-params(gen-id) move ty to decl-type(gen-id)
        move ind-source(i) to d
        move decl-name(d) to decl-induct(gen-id)
        move ind-all to decl-all(gen-id) move ind-nparams to decl-num-params(gen-id)
        move ind-count to decl-num-motives(gen-id)
        if ind-minors not = 0
            set address of list-arena to list-ptr move list-length(ind-minors) to decl-num-minors(gen-id)
        end-if
        set address of ind-arena to ind-ptr move ind-nindices(i) to decl-num-indices(gen-id)
        move rules to decl-rules(gen-id) move ind-k to decl-k(gen-id)
        move 2 to decl-status(gen-id) decl-replay(gen-id)
        move gen-id to name-env(rec-name)
    end-perform
    goback.
end program ind-build-recursors.
