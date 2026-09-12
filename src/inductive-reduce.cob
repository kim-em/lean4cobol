*> Iota reduction using regenerated recursor rules (Inductive/Reduce.lean).
identification division.
program-id. ind-reduce recursive.
data division.
local-storage section.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 major binary-long unsigned.
01 major-head binary-long unsigned.
01 major-args binary-long unsigned.
01 major-name binary-long unsigned.
01 name-id binary-long unsigned.
01 levels binary-long unsigned.
01 params binary-long unsigned.
01 d binary-long unsigned.
01 first-index binary-long unsigned.
01 major-index binary-long unsigned.
01 rule-list binary-long unsigned.
01 rule-id binary-long unsigned.
01 fields binary-long unsigned.
01 rhs-id binary-long unsigned.
01 current-id binary-long unsigned.
01 chosen binary-long unsigned.
01 start-index binary-long unsigned.
01 count-val binary-long unsigned.
01 tmp binary-long unsigned.
01 next-depth binary-long unsigned.
01 zero-val binary-long unsigned.
01 all-val binary-long unsigned value 4294967295.
01 k-flag binary-char unsigned.
01 parent-name binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
copy 'list.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-expr.
    move 0 to result-expr
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    if quot-initialized = 1
        call 'quot-reduce' using kernel-state input-expr next-depth result-expr
        if result-expr not = 0 or verdict not = 0 goback end-if
    end-if
    call 'expr-spine' using kernel-state input-expr head-id args
    set address of expr-arena to expr-ptr
    if expr-kind(head-id) not = 2 goback end-if
    move expr-a(head-id) to name-id move expr-b(head-id) to levels
    set address of name-arena to name-ptr move name-env(name-id) to d
    if d = 0 goback end-if
    set address of decl-arena to decl-ptr
    if decl-kind(d) not = 6 goback end-if
    compute first-index = decl-num-params(d) + decl-num-motives(d) + decl-num-minors(d)
    compute major-index = first-index + decl-num-indices(d)
    move decl-rules(d) to rule-list move decl-params(d) to params
    move decl-k(d) to k-flag move decl-induct(d) to parent-name
    call 'list-nth' using kernel-state args major-index major
    if major = 0 goback end-if
    if k-flag = 1
        call 'ind-to-ctor-k' using kernel-state d major next-depth tmp move tmp to major
    end-if
    call 'weak-head' using kernel-state major next-depth tmp move tmp to major
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    evaluate expr-kind(major)
      when 9
        call 'string-constructor' using kernel-state major tmp
        call 'weak-head' using kernel-state tmp next-depth major
      when 8
        call 'nat-constructor' using kernel-state major tmp move tmp to major
      when other
        call 'ind-to-ctor-struct' using kernel-state parent-name major next-depth tmp move tmp to major
    end-evaluate
    call 'expr-spine' using kernel-state major major-head major-args
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(major-head) not = 2 goback end-if
    move expr-a(major-head) to major-name
    perform until rule-list = 0
        set address of list-arena to list-ptr move list-a(rule-list) to rule-id
        set address of rule-arena to rule-ptr
        if rule-ctor(rule-id) = major-name exit perform end-if
        move list-b(rule-list) to rule-list
    end-perform
    if rule-list = 0 goback end-if
    move rule-fields(rule-id) to fields move rule-rhs(rule-id) to rhs-id
    move 0 to count-val
    if major-args not = 0
        set address of list-arena to list-ptr move list-length(major-args) to count-val
    end-if
    if fields > count-val goback end-if
    if params = 0 or levels = 0
        if params not = levels goback end-if
    else
        set address of list-arena to list-ptr
        if list-length(params) not = list-length(levels) goback end-if
    end-if
    call 'instantiate-constant-type' using kernel-state rhs-id params levels current-id
    call 'list-slice' using kernel-state args zero-val first-index chosen
    call 'expr-app-list' using kernel-state current-id chosen tmp move tmp to current-id
    move count-val to start-index
    subtract fields from start-index
    call 'list-slice' using kernel-state major-args start-index fields chosen
    call 'expr-app-list' using kernel-state current-id chosen tmp move tmp to current-id
    move major-index to start-index
    add 1 to start-index
    call 'list-slice' using kernel-state args start-index all-val chosen
    call 'expr-app-list' using kernel-state current-id chosen result-expr
    goback.
end program ind-reduce.

identification division.
program-id. ind-to-ctor-k recursive.
data division.
local-storage section.
01 ty binary-long unsigned.
01 app-type binary-long unsigned.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 levels binary-long unsigned.
01 name-id binary-long unsigned.
01 parent-name binary-long unsigned.
01 nparams binary-long unsigned.
01 parent-id binary-long unsigned.
01 ctors binary-long unsigned.
01 ctor-name binary-long unsigned.
01 ctor-id binary-long unsigned.
01 ctor-app binary-long unsigned.
01 chosen binary-long unsigned.
01 zero-val binary-long unsigned.
01 const-kind binary-long unsigned value 2.
01 answer binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
copy 'list.cpy'.
01 recursor-id binary-long unsigned.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state recursor-id input-expr depth-val result-expr.
    move input-expr to result-expr
    if verdict not = 0 goback end-if
    set address of decl-arena to decl-ptr
    move decl-induct(recursor-id) to parent-name move decl-num-params(recursor-id) to nparams
    call 'infer-only' using kernel-state input-expr depth-val ty
    call 'weak-head' using kernel-state ty depth-val app-type
    call 'expr-spine' using kernel-state app-type head-id args
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    if expr-kind(head-id) not = 2 goback end-if
    move expr-a(head-id) to name-id move expr-b(head-id) to levels
    if name-id not = parent-name goback end-if
    set address of name-arena to name-ptr move name-env(parent-name) to parent-id
    set address of decl-arena to decl-ptr move decl-ctors(parent-id) to ctors
    if ctors = 0 goback end-if
    set address of list-arena to list-ptr move list-a(ctors) to ctor-name
    call 'expr-intern' using kernel-state const-kind ctor-name levels zero-val zero-val ctor-id
    call 'list-slice' using kernel-state args zero-val nparams chosen
    call 'expr-app-list' using kernel-state ctor-id chosen ctor-app
    call 'infer-only' using kernel-state ctor-app depth-val ty
    call 'def-equal' using kernel-state app-type ty depth-val answer
    if verdict = 0 and answer = 1 move ctor-app to result-expr end-if
    goback.
end program ind-to-ctor-k.
