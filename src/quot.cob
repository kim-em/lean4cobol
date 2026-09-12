*> Lean4Lean/Quot.lean: validate Eq, construct four quotient declarations,
*> and reduce Quot.lift/Quot.ind. Exported quotient headers are not trusted.
identification division.
program-id. initialize-quot.
data division.
local-storage section.
01 eq-name binary-long unsigned.
01 quot-name binary-long unsigned.
01 mk-name binary-long unsigned.
01 lift-name binary-long unsigned.
01 ind-name binary-long unsigned.
01 u-name binary-long unsigned.
01 v-name binary-long unsigned.
01 u-level binary-long unsigned.
01 v-level binary-long unsigned.
01 u-levels binary-long unsigned.
01 v-levels binary-long unsigned.
01 u-params binary-long unsigned.
01 uv-params binary-long unsigned.
01 prop-id binary-long unsigned.
01 sort-u binary-long unsigned.
01 sort-v binary-long unsigned.
01 alpha binary-long unsigned.
01 rel binary-long unsigned.
01 aval binary-long unsigned.
01 bval binary-long unsigned.
01 beta binary-long unsigned.
01 fn binary-long unsigned.
01 qval binary-long unsigned.
01 quot-r binary-long unsigned.
01 mk-a binary-long unsigned.
01 rab binary-long unsigned.
01 fa binary-long unsigned.
01 fb binary-long unsigned.
01 eq-app binary-long unsigned.
01 sanity binary-long unsigned.
01 ty binary-long unsigned.
01 tmp binary-long unsigned.
01 tmp2 binary-long unsigned.
01 binders binary-long unsigned.
01 ar-binders binary-long unsigned.
01 ab-binders binary-long unsigned.
01 q-kind binary-long unsigned.
01 zero-val binary-long unsigned.
01 one-val binary-long unsigned value 1.
01 const-kind binary-long unsigned value 2.
01 app-kind binary-long unsigned value 3.
01 param-kind binary-long unsigned value 4.
01 pi-kind binary-long unsigned value 5.
linkage section.
copy 'state.cpy'.
procedure division using kernel-state.
    if verdict not = 0 or quot-initialized = 1 goback end-if
    call 'check-quot-eq' using kernel-state
    if verdict not = 0 goback end-if
    call 'builtin-name' using kernel-state 'Eq' eq-name
    call 'builtin-name' using kernel-state 'Quot' quot-name
    call 'builtin-name' using kernel-state 'Quot.mk' mk-name
    call 'builtin-name' using kernel-state 'Quot.lift' lift-name
    call 'builtin-name' using kernel-state 'Quot.ind' ind-name
    call 'builtin-name' using kernel-state 'u' u-name
    call 'builtin-name' using kernel-state 'v' v-name
    call 'level-intern' using kernel-state param-kind u-name zero-val u-level
    call 'level-intern' using kernel-state param-kind v-name zero-val v-level
    call 'list-intern' using kernel-state u-level zero-val u-levels
    call 'list-intern' using kernel-state v-level zero-val v-levels
    call 'list-intern' using kernel-state u-name zero-val u-params
    call 'list-intern' using kernel-state v-name zero-val tmp
    call 'list-intern' using kernel-state u-name tmp uv-params
    call 'expr-intern' using kernel-state one-val one-val zero-val zero-val zero-val prop-id
    call 'expr-intern' using kernel-state one-val u-level zero-val zero-val zero-val sort-u
    call 'expr-intern' using kernel-state one-val v-level zero-val zero-val zero-val sort-v
    call 'local-fresh' using kernel-state sort-u zero-val alpha
    call 'expr-intern' using kernel-state pi-kind alpha prop-id zero-val zero-val tmp
    call 'expr-intern' using kernel-state pi-kind alpha tmp zero-val zero-val ty
    call 'local-fresh' using kernel-state ty zero-val rel
    call 'list-intern' using kernel-state rel zero-val tmp
    call 'list-intern' using kernel-state alpha tmp ar-binders
    call 'expr-bind-list' using kernel-state pi-kind ar-binders sort-u ty
    call 'quot-add' using kernel-state quot-name u-params ty q-kind
    call 'expr-intern' using kernel-state const-kind quot-name u-levels zero-val zero-val tmp
    call 'expr-intern' using kernel-state app-kind tmp alpha zero-val zero-val tmp2
    call 'expr-intern' using kernel-state app-kind tmp2 rel zero-val zero-val quot-r
    call 'local-fresh' using kernel-state alpha zero-val aval
    call 'list-intern' using kernel-state aval zero-val tmp
    call 'list-append' using kernel-state ar-binders tmp binders
    call 'expr-bind-list' using kernel-state pi-kind binders quot-r ty
    move 1 to q-kind
    call 'quot-add' using kernel-state mk-name u-params ty q-kind
    call 'local-fresh' using kernel-state sort-v zero-val beta
    call 'expr-intern' using kernel-state pi-kind alpha beta zero-val zero-val ty
    call 'local-fresh' using kernel-state ty zero-val fn
    call 'local-fresh' using kernel-state alpha zero-val bval
    call 'expr-intern' using kernel-state app-kind rel aval zero-val zero-val tmp
    call 'expr-intern' using kernel-state app-kind tmp bval zero-val zero-val rab
    call 'expr-intern' using kernel-state app-kind fn aval zero-val zero-val fa
    call 'expr-intern' using kernel-state app-kind fn bval zero-val zero-val fb
    call 'expr-intern' using kernel-state const-kind eq-name v-levels zero-val zero-val tmp
    call 'expr-intern' using kernel-state app-kind tmp beta zero-val zero-val tmp2
    call 'expr-intern' using kernel-state app-kind tmp2 fa zero-val zero-val tmp
    call 'expr-intern' using kernel-state app-kind tmp fb zero-val zero-val eq-app
    call 'expr-intern' using kernel-state pi-kind rab eq-app zero-val zero-val ty
    call 'list-intern' using kernel-state bval zero-val tmp
    call 'list-intern' using kernel-state aval tmp ab-binders
    call 'expr-bind-list' using kernel-state pi-kind ab-binders ty sanity
    call 'expr-intern' using kernel-state pi-kind quot-r beta zero-val zero-val tmp
    call 'expr-intern' using kernel-state pi-kind sanity tmp zero-val zero-val ty
    call 'list-intern' using kernel-state fn zero-val tmp
    call 'list-intern' using kernel-state beta tmp tmp2
    call 'list-append' using kernel-state ar-binders tmp2 binders
    call 'expr-bind-list' using kernel-state pi-kind binders ty tmp
    move 2 to q-kind
    call 'quot-add' using kernel-state lift-name uv-params tmp q-kind
    call 'expr-intern' using kernel-state const-kind mk-name u-levels zero-val zero-val tmp
    call 'expr-intern' using kernel-state app-kind tmp alpha zero-val zero-val tmp2
    call 'expr-intern' using kernel-state app-kind tmp2 rel zero-val zero-val tmp
    call 'expr-intern' using kernel-state app-kind tmp aval zero-val zero-val mk-a
    call 'expr-intern' using kernel-state pi-kind quot-r prop-id zero-val zero-val ty
    call 'local-fresh' using kernel-state ty zero-val beta
    call 'expr-intern' using kernel-state app-kind beta mk-a zero-val zero-val tmp
    call 'list-intern' using kernel-state aval zero-val binders
    call 'expr-bind-list' using kernel-state pi-kind binders tmp sanity
    call 'local-fresh' using kernel-state quot-r zero-val qval
    call 'expr-intern' using kernel-state app-kind beta qval zero-val zero-val tmp
    call 'list-intern' using kernel-state qval zero-val binders
    call 'expr-bind-list' using kernel-state pi-kind binders tmp tmp2
    call 'expr-intern' using kernel-state pi-kind sanity tmp2 zero-val zero-val ty
    call 'list-intern' using kernel-state beta zero-val tmp
    call 'list-append' using kernel-state ar-binders tmp binders
    call 'expr-bind-list' using kernel-state pi-kind binders ty tmp
    move 3 to q-kind
    call 'quot-add' using kernel-state ind-name u-params tmp q-kind
    if verdict = 0 move 1 to quot-initialized add 1 to checked-count end-if
    goback.
end program initialize-quot.

identification division.
program-id. quot-add.
data division.
local-storage section.
01 wanted binary-long unsigned.
01 width binary-long unsigned.
01 d binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
01 name-id binary-long unsigned.
01 params binary-long unsigned.
01 ty binary-long unsigned.
01 kind-val binary-long unsigned.
procedure division using kernel-state name-id params ty kind-val.
    if verdict not = 0 goback end-if
    set address of name-arena to name-ptr
    if name-env(name-id) not = 0 move 1 to verdict goback end-if
    compute wanted = decl-count + 1 move length of decl-node to width
    call 'arena-reserve' using decl-ptr decl-cap wanted width verdict
    if verdict not = 0 goback end-if
    set address of decl-arena to decl-ptr add 1 to decl-count move decl-count to d
    move name-id to decl-name(d) move params to decl-params(d) move ty to decl-type(d)
    move 7 to decl-kind(d) move kind-val to decl-quot-kind(d)
    move 2 to decl-status(d) decl-replay(d) move d to name-env(name-id)
    goback.
end program quot-add.

identification division.
program-id. check-quot-eq.
data division.
local-storage section.
01 eq-name binary-long unsigned.
01 d binary-long unsigned.
01 ctors binary-long unsigned.
01 ctor-name binary-long unsigned.
01 params binary-long unsigned.
01 u-name binary-long unsigned.
01 u-level binary-long unsigned.
01 levels binary-long unsigned.
01 prop-id binary-long unsigned.
01 alpha binary-long unsigned.
01 aval binary-long unsigned.
01 expected-type binary-long unsigned.
01 actual-type binary-long unsigned.
01 tmp binary-long unsigned.
01 tmp2 binary-long unsigned.
01 binders binary-long unsigned.
01 stage binary-long unsigned.
01 zero-val binary-long unsigned.
01 one-val binary-long unsigned value 1.
01 param-kind binary-long unsigned value 4.
01 const-kind binary-long unsigned value 2.
01 app-kind binary-long unsigned value 3.
01 pi-kind binary-long unsigned value 5.
linkage section.
copy 'state.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
copy 'list.cpy'.
procedure division using kernel-state.
    if verdict not = 0 goback end-if
    call 'builtin-name' using kernel-state 'Eq' eq-name
    set address of name-arena to name-ptr move name-env(eq-name) to d
    if d = 0 move 1 to verdict goback end-if
    set address of decl-arena to decl-ptr
    if decl-kind(d) not = 4 move 1 to verdict goback end-if
    move decl-ctors(d) to ctors
    if ctors = 0 move 1 to verdict goback end-if
    set address of list-arena to list-ptr
    if list-length(ctors) not = 1 move 1 to verdict goback end-if
    move list-a(ctors) to ctor-name
    call 'expr-intern' using kernel-state one-val one-val zero-val zero-val zero-val prop-id
    perform varying stage from 0 by 1 until stage > 1 or verdict not = 0
        set address of decl-arena to decl-ptr
        move decl-params(d) to params move decl-type(d) to actual-type
        if params = 0 move 1 to verdict goback end-if
        set address of list-arena to list-ptr
        if list-length(params) not = 1 move 1 to verdict goback end-if
        move list-a(params) to u-name
        call 'level-intern' using kernel-state param-kind u-name zero-val u-level
        call 'expr-intern' using kernel-state one-val u-level zero-val zero-val zero-val tmp
        call 'local-fresh' using kernel-state tmp zero-val alpha
        if stage = 0
            call 'expr-intern' using kernel-state pi-kind alpha prop-id zero-val zero-val tmp
            call 'expr-intern' using kernel-state pi-kind alpha tmp zero-val zero-val tmp2
            call 'list-intern' using kernel-state alpha zero-val binders
        else
            call 'local-fresh' using kernel-state alpha zero-val aval
            call 'list-intern' using kernel-state u-level zero-val levels
            call 'expr-intern' using kernel-state const-kind eq-name levels zero-val zero-val tmp
            call 'expr-intern' using kernel-state app-kind tmp alpha zero-val zero-val tmp2
            call 'expr-intern' using kernel-state app-kind tmp2 aval zero-val zero-val tmp
            call 'expr-intern' using kernel-state app-kind tmp aval zero-val zero-val tmp2
            call 'list-intern' using kernel-state aval zero-val tmp
            call 'list-intern' using kernel-state alpha tmp binders
        end-if
        call 'expr-bind-list' using kernel-state pi-kind binders tmp2 expected-type
        if verdict not = 0 goback end-if
        if expected-type not = actual-type move 1 to verdict goback end-if
        set address of name-arena to name-ptr move name-env(ctor-name) to d
        if d = 0 move 1 to verdict goback end-if
    end-perform
    goback.
end program check-quot-eq.

identification division.
program-id. quot-reduce recursive.
data division.
local-storage section.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 name-id binary-long unsigned.
01 major-index binary-long unsigned.
01 major binary-long unsigned.
01 normalized binary-long unsigned.
01 mk-head binary-long unsigned.
01 mk-args binary-long unsigned.
01 fn binary-long unsigned.
01 aval binary-long unsigned.
01 current-id binary-long unsigned.
01 rest binary-long unsigned.
01 start-index binary-long unsigned.
01 matched binary-char unsigned.
01 fn-index binary-long unsigned value 3.
01 arg-index binary-long unsigned value 2.
01 app-kind binary-long unsigned value 3.
01 zero-val binary-long unsigned.
01 all-val binary-long unsigned value 4294967295.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'list.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-expr.
    move 0 to result-expr
    call 'expr-spine' using kernel-state input-expr head-id args
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(head-id) not = 2 goback end-if
    move expr-a(head-id) to name-id
    call 'name-matches' using kernel-state name-id 'Quot.lift' matched
    if matched = 1 move 5 to major-index
    else
        call 'name-matches' using kernel-state name-id 'Quot.ind' matched
        if matched = 0 goback end-if
        move 4 to major-index
    end-if
    call 'list-nth' using kernel-state args major-index major
    if major = 0 goback end-if
    call 'weak-head' using kernel-state major depth-val normalized
    call 'expr-spine' using kernel-state normalized mk-head mk-args
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(mk-head) not = 2 or mk-args = 0 goback end-if
    move expr-a(mk-head) to name-id
    call 'name-matches' using kernel-state name-id 'Quot.mk' matched
    if matched = 0 goback end-if
    set address of list-arena to list-ptr
    if list-length(mk-args) not = 3 goback end-if
    call 'list-nth' using kernel-state mk-args arg-index aval
    call 'list-nth' using kernel-state args fn-index fn
    call 'expr-intern' using kernel-state app-kind fn aval zero-val zero-val current-id
    move major-index to start-index
    add 1 to start-index
    call 'list-slice' using kernel-state args start-index all-val rest
    call 'expr-app-list' using kernel-state current-id rest result-expr
    goback.
end program quot-reduce.
