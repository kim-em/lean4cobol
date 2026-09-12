*> Primitive.unfoldNatWellFounded, including validation of fix.go and the
*> eager fuel wrapper. The eq_def inputs are kernel-owned pinned quotations.
identification division.
program-id. unfold-nat-well-founded.
data division.
local-storage section.
copy 'reflection.cpy'.
01 current-id binary-long unsigned.
01 tmp binary-long unsigned.
01 tmp2 binary-long unsigned.
01 left-id binary-long unsigned.
01 right-id binary-long unsigned.
01 original-head binary-long unsigned.
01 equation-rhs binary-long unsigned.
01 head-id binary-long unsigned.
01 args binary-long unsigned.
01 p binary-long unsigned.
01 n binary-long unsigned.
01 levels binary-long unsigned.
01 expected-count binary-long unsigned.
01 fixed-arguments.
   02 fixed-arg binary-long unsigned occurs 4.
01 i binary-long unsigned.
01 measure-id binary-long unsigned.
01 functional-id binary-long unsigned.
01 initial-id binary-long unsigned.
01 fix-fn binary-long unsigned.
01 fix-go binary-long unsigned.
01 local-a binary-long unsigned.
01 fuel-id binary-long unsigned.
01 eager-id binary-long unsigned.
01 succ-fn binary-long unsigned.
01 locals-list binary-long unsigned.
01 functional-local binary-long unsigned.
01 fuel-local binary-long unsigned.
01 nat-rec binary-long unsigned.
01 local-x binary-long unsigned.
01 local-y binary-long unsigned.
01 ih-id binary-long unsigned.
01 zero-bvar binary-long unsigned.
01 zero-val binary-long unsigned.
01 one-val binary-long unsigned value 1.
01 reverse-mode binary-long unsigned value 2.
01 const-kind binary-long unsigned value 2.
01 app-kind binary-long unsigned value 3.
01 lam-kind binary-long unsigned value 4.
01 pi-kind binary-long unsigned value 5.
01 condition-kind binary-long unsigned.
01 need-ite binary-char unsigned value 1.
01 need-dite binary-char unsigned.
01 answer binary-char unsigned.
01 matched binary-char unsigned.
01 stage binary-long unsigned.
01 trace-option pic x.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'list.cpy'.
copy 'names.cpy'.
01 candidate binary-long unsigned.
01 parameters binary-long unsigned.
01 equation-type binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state candidate parameters equation-type depth-val result-expr.
    move 0 to result-expr
    if verdict not = 0 goback end-if
    perform validate-fix
    if verdict not = 0
        accept trace-option from environment 'LEAN4COBOL_TRACE' on exception move space to trace-option end-accept
        if trace-option = '1' display 'well-founded check failed at stage ' stage upon syserr end-if
    end-if
    goback.
validate-fix.
    move 1 to stage
    move equation-type to current-id
    set address of expr-arena to expr-ptr
    perform until expr-kind(current-id) not = 5 move expr-b(current-id) to current-id end-perform
    call 'expr-instantiate-list' using kernel-state current-id parameters reverse-mode tmp
    if verdict not = 0 exit paragraph end-if
    set address of expr-arena to expr-ptr
    if expr-kind(tmp) not = 3 move 1 to verdict exit paragraph end-if
    move expr-b(tmp) to right-id move expr-a(tmp) to tmp
    if expr-kind(tmp) not = 3 move 1 to verdict exit paragraph end-if
    move expr-b(tmp) to left-id
    call 'expr-spine' using kernel-state left-id original-head args
    call 'expr-replace-exact' using kernel-state right-id original-head candidate equation-rhs
    call 'builtin-name' using kernel-state 'Nat.succ' n
    call 'expr-intern' using kernel-state const-kind n zero-val zero-val zero-val succ-fn

    move 2 to stage
    call 'expr-app-list' using kernel-state candidate parameters tmp
    call 'weak-head-core' using kernel-state tmp depth-val tmp2
    call 'unfold-head' using kernel-state tmp2 depth-val current-id
    if current-id = 0 or verdict not = 0 perform fail-shape exit paragraph end-if
    call 'weak-head-core' using kernel-state current-id depth-val tmp
    call 'expr-spine' using kernel-state tmp head-id args
    move 5 to expected-count perform expect-arity
    if verdict not = 0 exit paragraph end-if
    set address of expr-arena to expr-ptr
    if expr-kind(head-id) not = 2 move 1 to verdict exit paragraph end-if
    move expr-a(head-id) to n move expr-b(head-id) to levels
    call 'name-matches' using kernel-state n 'WellFounded.Nat.fix' matched
    if matched = 0 or levels = 0 move 1 to verdict exit paragraph end-if
    set address of list-arena to list-ptr
    if list-length(levels) not = 2 move 1 to verdict exit paragraph end-if
    move args to p
    perform varying i from 1 by 1 until i > 4
        move list-a(p) to fixed-arg(i) move list-b(p) to p
    end-perform
    move fixed-arg(3) to measure-id move fixed-arg(4) to functional-id
    move list-a(p) to initial-id
    move 4 to expected-count
    call 'list-slice' using kernel-state args zero-val expected-count p
    call 'expr-app-list' using kernel-state head-id p fix-fn
    call 'infer-only' using kernel-state initial-id depth-val tmp
    call 'local-fresh' using kernel-state tmp zero-val local-a

    move 3 to stage
    call 'expr-intern' using kernel-state app-kind fix-fn local-a zero-val zero-val tmp
    call 'unfold-head' using kernel-state tmp depth-val current-id
    if current-id = 0 or verdict not = 0 perform fail-shape exit paragraph end-if
    call 'weak-head-core' using kernel-state current-id depth-val tmp
    call 'expr-spine' using kernel-state tmp fix-go args
    move 7 to expected-count perform expect-arity
    if verdict not = 0 exit paragraph end-if
    set address of list-arena to list-ptr move args to p
    perform varying i from 1 by 1 until i > 4
        if fixed-arg(i) not = list-a(p) move 1 to verdict exit paragraph end-if
        move list-b(p) to p
    end-perform
    move list-a(p) to fuel-id move list-b(p) to p
    if list-a(p) not = local-a move 1 to verdict exit paragraph end-if
    set address of expr-arena to expr-ptr
    if expr-kind(fuel-id) not = 3 move 1 to verdict exit paragraph end-if
    move expr-a(fuel-id) to eager-id move expr-b(fuel-id) to left-id
    call 'expr-intern' using kernel-state app-kind measure-id local-a zero-val zero-val tmp
    call 'expr-intern' using kernel-state app-kind succ-fn tmp zero-val zero-val right-id
    perform require-equal
    if verdict not = 0 exit paragraph end-if

    move 4 to stage
    call 'builtin-name' using kernel-state 'Nat.beq' n
    set address of name-arena to name-ptr
    if name-env(n) = 0 move 1 to verdict exit paragraph end-if
    call 'check-condition' using kernel-state reflection-context condition-kind need-ite need-dite depth-val
    move eager-id to rc-a
    call 'reflection-quote' using kernel-state reflection-context 'wf.eagerLhs' left-id
    call 'reflection-quote' using kernel-state reflection-context 'wf.eagerRhs' right-id
    perform require-equal
    if verdict not = 0 exit paragraph end-if

    move 5 to stage
    call 'unfold-head' using kernel-state fix-go depth-val current-id
    if current-id = 0 or verdict not = 0 perform fail-shape exit paragraph end-if
    call 'primitive-telescope' using kernel-state current-id lam-kind locals-list tmp
    move locals-list to args move 5 to expected-count perform expect-arity
    if verdict not = 0 exit paragraph end-if
    move 3 to i call 'list-nth' using kernel-state locals-list i functional-local
    move 4 to i call 'list-nth' using kernel-state locals-list i fuel-local
    set address of expr-arena to expr-ptr
    if expr-kind(tmp) not = 3 move 1 to verdict exit paragraph end-if
    move expr-a(tmp) to nat-rec
    if expr-b(tmp) not = fuel-local move 1 to verdict exit paragraph end-if
    call 'expr-intern' using kernel-state zero-val zero-val zero-val zero-val zero-val zero-bvar
    call 'expr-replace-exact' using kernel-state nat-rec fuel-local zero-bvar tmp
    if tmp not = nat-rec or verdict not = 0 perform fail-shape exit paragraph end-if
    call 'expr-intern' using kernel-state app-kind succ-fn fuel-local zero-val zero-val tmp
    call 'infer-type' using kernel-state tmp depth-val tmp2
    call 'expr-intern' using kernel-state app-kind nat-rec tmp zero-val zero-val current-id
    call 'weak-head-core' using kernel-state current-id depth-val tmp
    call 'primitive-telescope' using kernel-state tmp lam-kind locals-list current-id
    move locals-list to args move 2 to expected-count perform expect-arity
    if verdict not = 0 exit paragraph end-if
    call 'list-nth' using kernel-state locals-list zero-val local-x
    set address of expr-arena to expr-ptr
    if expr-kind(current-id) not = 3 move 1 to verdict exit paragraph end-if
    move expr-a(current-id) to left-id move expr-b(current-id) to ih-id
    call 'expr-intern' using kernel-state app-kind functional-local local-x zero-val zero-val right-id
    if left-id not = right-id move 1 to verdict exit paragraph end-if

    move 6 to stage
    call 'primitive-telescope' using kernel-state ih-id lam-kind locals-list current-id
    move locals-list to args move 2 to expected-count perform expect-arity
    if verdict not = 0 exit paragraph end-if
    call 'list-nth' using kernel-state locals-list zero-val local-y
    set address of expr-arena to expr-ptr
    if expr-kind(current-id) not = 3 move 1 to verdict exit paragraph end-if
    move expr-a(current-id) to left-id
    call 'expr-intern' using kernel-state app-kind nat-rec fuel-local zero-val zero-val tmp
    call 'expr-intern' using kernel-state app-kind tmp local-y zero-val zero-val right-id
    if left-id not = right-id move 1 to verdict exit paragraph end-if

    move 7 to stage
    call 'expr-intern' using kernel-state app-kind functional-id initial-id zero-val zero-val current-id
    call 'infer-only' using kernel-state current-id depth-val tmp
    if verdict not = 0 exit paragraph end-if
    set address of expr-arena to expr-ptr
    if expr-kind(tmp) not = 5 move 1 to verdict exit paragraph end-if
    move expr-a(tmp) to tmp2
    call 'primitive-telescope' using kernel-state tmp2 pi-kind locals-list tmp
    move locals-list to args move 2 to expected-count perform expect-arity
    if verdict not = 0 exit paragraph end-if
    call 'list-nth' using kernel-state locals-list zero-val local-y
    call 'expr-intern' using kernel-state app-kind fix-fn local-y zero-val zero-val tmp
    call 'expr-bind-list' using kernel-state lam-kind locals-list tmp ih-id
    call 'expr-intern' using kernel-state app-kind current-id ih-id zero-val zero-val right-id
    call 'infer-type' using kernel-state right-id depth-val tmp
    move equation-rhs to left-id perform require-equal
    call 'expr-bind-list' using kernel-state lam-kind parameters equation-rhs result-expr.
expect-arity.
    if verdict not = 0 exit paragraph end-if
    if args = 0 move 1 to verdict exit paragraph end-if
    set address of list-arena to list-ptr
    if list-length(args) not = expected-count move 1 to verdict end-if.
require-equal.
    if verdict not = 0 exit paragraph end-if
    call 'def-equal' using kernel-state left-id right-id depth-val answer
    if verdict = 0 and answer = 0 move 1 to verdict end-if.
fail-shape.
    if verdict = 0 move 1 to verdict end-if.
end program unfold-nat-well-founded.

identification division.
program-id. check-wf-primitive.
data division.
local-storage section.
copy 'reflection.cpy'.
01 name-id binary-long unsigned.
01 actual-type binary-long unsigned.
01 expected-type binary-long unsigned.
01 nat-type binary-long unsigned.
01 function-type binary-long unsigned.
01 equation-type binary-long unsigned.
01 parameters binary-long unsigned.
01 tmp binary-long unsigned.
01 left-id binary-long unsigned.
01 right-id binary-long unsigned.
01 condition-kind binary-long unsigned.
01 zero-val binary-long unsigned.
01 answer binary-char unsigned.
01 need-ite binary-char unsigned value 1.
01 need-dite binary-char unsigned.
01 stage binary-long unsigned.
01 trace-option pic x.
linkage section.
copy 'state.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
01 declaration-id binary-long unsigned.
01 primitive-id binary-long unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state declaration-id primitive-id depth-val.
    if verdict not = 0 goback end-if
    perform validate-primitive
    if verdict not = 0
        accept trace-option from environment 'LEAN4COBOL_TRACE' on exception move space to trace-option end-accept
        if trace-option = '1' display 'well-founded primitive ' primitive-id ' failed at stage ' stage upon syserr end-if
    end-if
    goback.
validate-primitive.
    move 1 to stage
    set address of decl-arena to decl-ptr
    move decl-value(declaration-id) to rc-value move decl-type(declaration-id) to actual-type
    if primitive-id = 17
        call 'builtin-name' using kernel-state 'Nat.mod' name-id perform require-name
        call 'primitive-template' using kernel-state rc-value 'Nat Nat Nat > >' expected-type
        call 'reflection-quote' using kernel-state reflection-context 'wf.gcdEqDef' equation-type
    else
        call 'builtin-name' using kernel-state 'Nat' name-id perform require-name
        call 'builtin-name' using kernel-state 'Bool' name-id perform require-name
        call 'reflection-quote' using kernel-state reflection-context 'bitwise.type' expected-type
        call 'reflection-quote' using kernel-state reflection-context 'wf.bitwiseEqDef' equation-type
    end-if
    call 'def-equal' using kernel-state actual-type expected-type depth-val answer
    if verdict = 0 and answer = 0 move 1 to verdict end-if
    if verdict not = 0 exit paragraph end-if
    if primitive-id = 18
        move 2 to condition-kind
        call 'check-condition' using kernel-state reflection-context condition-kind need-ite need-dite depth-val
        move 0 to condition-kind
        call 'check-condition' using kernel-state reflection-context condition-kind need-ite need-dite depth-val
        call 'reflection-quote' using kernel-state reflection-context 'bitwise.functionType' function-type
        call 'local-fresh' using kernel-state function-type zero-val rc-a
    end-if
    call 'reflection-quote' using kernel-state reflection-context 'Nat' nat-type
    call 'local-fresh' using kernel-state nat-type zero-val rc-x
    call 'local-fresh' using kernel-state nat-type zero-val rc-y
    call 'list-intern' using kernel-state rc-y zero-val tmp
    call 'list-intern' using kernel-state rc-x tmp parameters
    if primitive-id = 18
        call 'list-intern' using kernel-state rc-a parameters tmp move tmp to parameters
    end-if
    move 2 to stage
    call 'unfold-nat-well-founded' using kernel-state rc-value parameters equation-type depth-val rc-go
    if verdict not = 0 exit paragraph end-if
    move 3 to stage
    if primitive-id = 17
        call 'reflection-quote' using kernel-state reflection-context 'gcd.zeroLhs' left-id
        move rc-x to right-id perform require-equal
        call 'reflection-quote' using kernel-state reflection-context 'gcd.succLhs' left-id
        call 'reflection-quote' using kernel-state reflection-context 'gcd.succRhs' right-id
        perform require-equal
    else
        call 'reflection-quote' using kernel-state reflection-context 'bitwise.rhs' right-id
        call 'infer-type' using kernel-state right-id depth-val tmp
        call 'reflection-quote' using kernel-state reflection-context 'bitwise.lhs' left-id
        perform require-equal
    end-if.
require-name.
    if verdict not = 0 exit paragraph end-if
    set address of name-arena to name-ptr
    if name-env(name-id) = 0 move 1 to verdict end-if.
require-equal.
    if verdict not = 0 exit paragraph end-if
    call 'def-equal' using kernel-state left-id right-id depth-val answer
    if verdict = 0 and answer = 0 move 1 to verdict end-if.
end program check-wf-primitive.
