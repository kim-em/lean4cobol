*> Primitive.lean Reflection.check/checkITE/checkNatDITE and Condition.check.
identification division.
program-id. reflection-assert.
data division.
local-storage section.
01 actual-expr binary-long unsigned.
01 expected-expr binary-long unsigned.
01 answer binary-char unsigned.
01 trace-option pic x.
linkage section.
copy 'state.cpy'.
copy 'reflection.cpy'.
01 input-expr binary-long unsigned.
01 expected-name pic x any length.
01 check-mode binary-long unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state reflection-context input-expr expected-name check-mode depth-val.
    if verdict not = 0 goback end-if
    move input-expr to actual-expr
    evaluate check-mode
      when 1 call 'infer-type' using kernel-state input-expr depth-val actual-expr
      when 2 call 'infer-only' using kernel-state input-expr depth-val actual-expr
    end-evaluate
    call 'reflection-quote' using kernel-state reflection-context expected-name expected-expr
    call 'def-equal' using kernel-state actual-expr expected-expr depth-val answer
    if verdict = 0 and answer = 0 move 1 to verdict end-if
    if verdict not = 0
        accept trace-option from environment 'LEAN4COBOL_TRACE'
            on exception move space to trace-option
        end-accept
        if trace-option = '1' display 'reflection check failed: ' expected-name upon syserr end-if
    end-if
    goback.
end program reflection-assert.

identification division.
program-id. check-reflection.
data division.
local-storage section.
01 term binary-long unsigned.
01 ty binary-long unsigned.
01 zero-val binary-long unsigned.
01 checking binary-long unsigned value 1.
linkage section.
copy 'state.cpy'.
copy 'reflection.cpy'.
01 need-ite binary-char unsigned.
01 need-dite binary-char unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state reflection-context need-ite need-dite depth-val.
    if verdict not = 0 goback end-if
    call 'reflection-assert' using kernel-state reflection-context rc-r-type 'r.typeExpected' checking depth-val
    if need-ite = 1 and verdict = 0
        call 'reflection-assert' using kernel-state reflection-context rc-r-ite 'r.iteExpected' checking depth-val
        call 'reflection-quote' using kernel-state reflection-context 'Prop' ty
        call 'local-fresh' using kernel-state ty zero-val rc-p
        call 'reflection-quote' using kernel-state reflection-context 'r.trueHyp' ty
        call 'local-fresh' using kernel-state ty zero-val rc-hyp
        call 'reflection-quote' using kernel-state reflection-context 'r.iteTrue' term
        call 'reflection-assert' using kernel-state reflection-context term 'r.iteTrueExpected' zero-val depth-val
        call 'reflection-quote' using kernel-state reflection-context 'r.falseHyp' ty
        call 'local-fresh' using kernel-state ty zero-val rc-hyp
        call 'reflection-quote' using kernel-state reflection-context 'r.iteFalse' term
        call 'reflection-assert' using kernel-state reflection-context term 'r.iteFalseExpected' zero-val depth-val
    end-if
    if need-dite = 1 and verdict = 0
        call 'reflection-quote' using kernel-state reflection-context 'Not' term
        call 'reflection-assert' using kernel-state reflection-context term 'not.type' checking depth-val
        call 'reflection-assert' using kernel-state reflection-context rc-r-dite 'r.diteExpected' checking depth-val
        call 'reflection-assert' using kernel-state reflection-context rc-r-true 'r.trueExpected' checking depth-val
        call 'reflection-assert' using kernel-state reflection-context rc-r-false 'r.falseExpected' checking depth-val
        call 'reflection-quote' using kernel-state reflection-context 'Prop' ty
        call 'local-fresh' using kernel-state ty zero-val rc-p
        call 'reflection-quote' using kernel-state reflection-context 'r.aType' ty
        call 'local-fresh' using kernel-state ty zero-val rc-a
        call 'reflection-quote' using kernel-state reflection-context 'r.bType' ty
        call 'local-fresh' using kernel-state ty zero-val rc-b
        call 'reflection-quote' using kernel-state reflection-context 'r.trueHyp' ty
        call 'local-fresh' using kernel-state ty zero-val rc-hyp
        call 'reflection-quote' using kernel-state reflection-context 'r.diteTrue' term
        call 'reflection-assert' using kernel-state reflection-context term 'r.diteTrueExpected' zero-val depth-val
        call 'reflection-quote' using kernel-state reflection-context 'r.falseHyp' ty
        call 'local-fresh' using kernel-state ty zero-val rc-hyp
        call 'reflection-quote' using kernel-state reflection-context 'r.diteFalse' term
        call 'reflection-assert' using kernel-state reflection-context term 'r.diteFalseExpected' zero-val depth-val
    end-if
    goback.
end program check-reflection.

identification division.
program-id. check-condition.
data division.
local-storage section.
01 term binary-long unsigned.
01 ty binary-long unsigned.
01 universe-id binary-long unsigned.
01 answer binary-char unsigned.
01 zero-val binary-long unsigned.
01 checking binary-long unsigned value 1.
01 known-type binary-long unsigned value 2.
linkage section.
copy 'state.cpy'.
copy 'reflection.cpy'.
copy 'levels.cpy'.
01 condition-kind binary-long unsigned.
01 need-ite binary-char unsigned.
01 need-dite binary-char unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state reflection-context condition-kind need-ite need-dite depth-val.
    if verdict not = 0 goback end-if
    evaluate condition-kind
      when 0
        call 'reflection-quote' using kernel-state reflection-context 'bool.prop' rc-c-prop
        call 'reflection-quote' using kernel-state reflection-context 'bool.dec' rc-c-dec
      when 1
        call 'reflection-quote' using kernel-state reflection-context 'le.prop' rc-c-prop
        call 'reflection-quote' using kernel-state reflection-context 'le.dec' rc-c-dec
        call 'reflection-quote' using kernel-state reflection-context 'le.asBool' rc-as-bool
        call 'reflection-quote' using kernel-state reflection-context 'le.proof' rc-c-proof
        call 'reflection-quote' using kernel-state reflection-context 'r1.type' rc-r-type
        call 'reflection-quote' using kernel-state reflection-context 'r1.true' rc-r-true
        call 'reflection-quote' using kernel-state reflection-context 'r1.false' rc-r-false
        call 'reflection-quote' using kernel-state reflection-context 'r1.dec' rc-r-dec
        call 'reflection-quote' using kernel-state reflection-context 'r1.ite' rc-r-ite
        call 'reflection-quote' using kernel-state reflection-context 'r1.dite' rc-r-dite
      when 2
        call 'reflection-quote' using kernel-state reflection-context 'eq.prop' rc-c-prop
        call 'reflection-quote' using kernel-state reflection-context 'eq.dec' rc-c-dec
        call 'reflection-quote' using kernel-state reflection-context 'eq.asBool' rc-as-bool
        call 'reflection-quote' using kernel-state reflection-context 'eq.proof' rc-c-proof
        call 'reflection-quote' using kernel-state reflection-context 'r2.type' rc-r-type
        call 'reflection-quote' using kernel-state reflection-context 'r2.true' rc-r-true
        call 'reflection-quote' using kernel-state reflection-context 'r2.false' rc-r-false
        call 'reflection-quote' using kernel-state reflection-context 'r2.dec' rc-r-dec
        call 'reflection-quote' using kernel-state reflection-context 'r2.ite' rc-r-ite
        call 'reflection-quote' using kernel-state reflection-context 'r2.dite' rc-r-dite
      when other move 3 to verdict goback
    end-evaluate
    call 'infer-type' using kernel-state rc-c-dec depth-val ty
    if condition-kind = 0
        call 'reflection-assert' using kernel-state reflection-context rc-c-prop 'bool.propExpected' known-type depth-val
        if need-ite = 1 and verdict = 0
            call 'reflection-quote' using kernel-state reflection-context 'bool.natITE' rc-r-ite
            call 'reflection-assert' using kernel-state reflection-context rc-r-ite 'bool.iteExpected' checking depth-val
            call 'reflection-quote' using kernel-state reflection-context 'bool.iteTrue' term
            call 'reflection-assert' using kernel-state reflection-context term 'bool.iteTrueExpected' zero-val depth-val
            call 'reflection-quote' using kernel-state reflection-context 'bool.iteFalse' term
            call 'reflection-assert' using kernel-state reflection-context term 'bool.iteFalseExpected' zero-val depth-val
        end-if
        if need-dite = 1 and verdict = 0 move 1 to verdict end-if
        goback
    end-if
    call 'reflection-assert' using kernel-state reflection-context rc-c-prop 'c.propExpected' known-type depth-val
    call 'check-reflection' using kernel-state reflection-context need-ite need-dite depth-val
    call 'reflection-quote' using kernel-state reflection-context 'c.decBody' term
    call 'infer-type' using kernel-state term depth-val ty
    call 'reflection-assert' using kernel-state reflection-context rc-as-bool 'c.boolExpected' known-type depth-val
    call 'infer-only' using kernel-state rc-c-proof depth-val ty
    call 'type-sort-level' using kernel-state ty depth-val universe-id
    if verdict not = 0 goback end-if
    set address of level-arena to level-ptr
    if level-always-zero(universe-id) = 0 move 1 to verdict goback end-if
    call 'def-equal' using kernel-state term rc-c-dec depth-val answer
    if verdict = 0 and answer = 0 move 1 to verdict end-if
    goback.
end program check-condition.

*> Primitive.lean: Nat.mod and Nat.div share fuel-recursion validation.
identification division.
program-id. check-division-primitive.
data division.
local-storage section.
copy 'reflection.cpy'.
01 need-ite binary-char unsigned.
01 need-dite binary-char unsigned value 1.
01 condition-kind binary-long unsigned value 1.
01 term binary-long unsigned.
01 ty binary-long unsigned.
01 nat-type binary-long unsigned.
01 lhs binary-long unsigned.
01 zero-val binary-long unsigned.
01 checking binary-long unsigned value 1.
01 expected-name pic x(40).
linkage section.
copy 'state.cpy'.
copy 'declarations.cpy'.
01 declaration-id binary-long unsigned.
01 primitive-id binary-long unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state declaration-id primitive-id depth-val.
    if verdict not = 0 goback end-if
    set address of decl-arena to decl-ptr move decl-value(declaration-id) to rc-value
    if primitive-id = 15
        call 'reflection-quote' using kernel-state reflection-context 'mod.zero' term
        call 'reflection-assert' using kernel-state reflection-context term 'mod.zeroExpected' zero-val depth-val
        move 1 to need-ite
    else
        call 'check-condition' using kernel-state reflection-context condition-kind need-ite need-dite depth-val
    end-if
    call 'reflection-quote' using kernel-state reflection-context 'le.prop' term
    call 'reflection-assert' using kernel-state reflection-context term 'c.propExpected' checking depth-val
    if primitive-id = 15
        call 'reflection-quote' using kernel-state reflection-context 'mod.go' rc-go
    else
        call 'reflection-quote' using kernel-state reflection-context 'div.go' rc-go
    end-if
    call 'reflection-assert' using kernel-state reflection-context rc-go 'division.goType' checking depth-val
    if primitive-id = 15
        call 'check-condition' using kernel-state reflection-context condition-kind need-ite need-dite depth-val
    end-if
    call 'reflection-quote' using kernel-state reflection-context 'Nat' nat-type
    call 'local-fresh' using kernel-state nat-type zero-val rc-x
    call 'local-fresh' using kernel-state nat-type zero-val rc-y
    if primitive-id = 15 move 'mod.initial' to expected-name
    else move 'div.initial' to expected-name end-if
    call 'reflection-quote' using kernel-state reflection-context expected-name term
    call 'infer-type' using kernel-state term depth-val ty
    if primitive-id = 15
        call 'reflection-quote' using kernel-state reflection-context 'mod.initialLhs' lhs
    else
        call 'reflection-quote' using kernel-state reflection-context 'div.initialLhs' lhs
    end-if
    call 'reflection-assert' using kernel-state reflection-context lhs expected-name zero-val depth-val
    call 'reflection-quote' using kernel-state reflection-context 'division.hyType' ty
    call 'local-fresh' using kernel-state ty zero-val rc-hy
    call 'local-fresh' using kernel-state nat-type zero-val rc-fuel
    call 'reflection-quote' using kernel-state reflection-context 'division.hType' ty
    call 'local-fresh' using kernel-state ty zero-val rc-h
    if primitive-id = 15 move 'mod.recursive' to expected-name
    else move 'div.recursive' to expected-name end-if
    call 'reflection-quote' using kernel-state reflection-context expected-name term
    call 'infer-type' using kernel-state term depth-val ty
    call 'reflection-quote' using kernel-state reflection-context 'division.recursiveLhs' lhs
    call 'reflection-assert' using kernel-state reflection-context lhs expected-name zero-val depth-val
    goback.
end program check-division-primitive.
