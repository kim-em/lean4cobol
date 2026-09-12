*> Primitive.lean/checkPrimitiveDef. Equations use the candidate body before
*> its name is installed in the checked environment, so native reduction cannot
*> certify a forged implementation of a primitive.
identification division.
program-id. check-primitive-definition.
data division.
local-storage section.
01 name-id binary-long unsigned.
01 body-id binary-long unsigned.
01 actual-type binary-long unsigned.
01 expected-type binary-long unsigned.
01 left-expr binary-long unsigned.
01 right-expr binary-long unsigned.
01 tmp binary-long unsigned.
01 nat-type binary-long unsigned.
01 primitive-id binary-long unsigned.
01 depth-val binary-long unsigned.
01 bind-count binary-long unsigned.
01 k binary-long unsigned.
01 zero-val binary-long unsigned.
01 pi-kind binary-long unsigned value 5.
01 answer binary-char unsigned.
01 matched binary-char unsigned.
01 spelling pic x(32).
01 trace-option pic x.
01 left-template pic x(512).
01 right-template pic x(512).
linkage section.
copy 'state.cpy'.
copy 'names.cpy'.
copy 'declarations.cpy'.
copy 'expr.cpy'.
01 declaration-id binary-long unsigned.
procedure division using kernel-state declaration-id.
    if verdict not = 0 goback end-if
    set address of decl-arena to decl-ptr
    move decl-name(declaration-id) to name-id
    move decl-value(declaration-id) to body-id
    move decl-type(declaration-id) to actual-type
    if decl-params(declaration-id) not = 0 move 1 to verdict goback end-if
    call 'name-matches' using kernel-state name-id 'Nat.add' matched
    if matched = 1 move 1 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.pred' matched
    if matched = 1 move 2 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.sub' matched
    if matched = 1 move 3 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.mul' matched
    if matched = 1 move 4 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.pow' matched
    if matched = 1 move 5 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.beq' matched
    if matched = 1 move 6 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.ble' matched
    if matched = 1 move 7 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.shiftLeft' matched
    if matched = 1 move 8 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.shiftRight' matched
    if matched = 1 move 9 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.land' matched
    if matched = 1 move 10 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.lor' matched
    if matched = 1 move 11 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.xor' matched
    if matched = 1 move 12 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Char.ofNat' matched
    if matched = 1 move 13 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'String.ofList' matched
    if matched = 1 move 14 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.mod' matched
    if matched = 1 move 15 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.div' matched
    if matched = 1 move 16 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.gcd' matched
    if matched = 1 move 17 to primitive-id end-if
    call 'name-matches' using kernel-state name-id 'Nat.bitwise' matched
    if matched = 1 move 18 to primitive-id end-if
    if primitive-id = 0 move 1 to verdict goback end-if
    *> Reflection and well-founded recursion validation is ported separately.
    if primitive-id >= 17
        call 'check-wf-primitive' using kernel-state declaration-id primitive-id depth-val
        goback
    end-if
    evaluate primitive-id
      when 3 move 'Nat.pred' to spelling
      when 4 move 'Nat.add' to spelling
      when 5 when 8 move 'Nat.mul' to spelling
      when 9 move 'Nat.div' to spelling
      when 10 when 11 when 12 move 'Nat.bitwise' to spelling
      when 15 when 16 move 'Nat.sub' to spelling
      when 14 move spaces to spelling
      when other move 'Nat' to spelling
    end-evaluate
    if spelling not = spaces perform require-constant end-if
    if primitive-id = 6 or 7 or 15 or 16
        move 'Bool' to spelling perform require-constant
    end-if
    if verdict not = 0 goback end-if
    call 'primitive-template' using kernel-state body-id 'Nat' nat-type
    evaluate primitive-id
      when 2 move 'Nat Nat >' to right-template
      when 6 when 7 move 'Nat Nat Bool > >' to right-template
      when 13 move 'Nat Char >' to right-template
      when 14 move 'List.0 Char @ String >' to right-template
      when other move 'Nat Nat Nat > >' to right-template
    end-evaluate
    call 'primitive-template' using kernel-state body-id right-template expected-type
    call 'def-equal' using kernel-state actual-type expected-type depth-val answer
    if verdict not = 0 goback end-if
    if answer = 0 move 1 to verdict goback end-if
    evaluate primitive-id
      when 15 when 16
        call 'check-division-primitive' using kernel-state declaration-id primitive-id depth-val
      when 1
        move 1 to bind-count
        move '$ #0 @ Nat.zero @' to left-template
        move '#0' to right-template
        perform check-equation
        move 2 to bind-count
        move '$ #1 @ Nat.succ #0 @ @' to left-template
        move 'Nat.succ $ #1 @ #0 @ @' to right-template
        perform check-equation
      when 2
        move 0 to bind-count
        move '$ Nat.zero @' to left-template
        move 'Nat.zero' to right-template
        perform check-equation
        move 1 to bind-count
        move '$ Nat.succ #0 @ @' to left-template
        move '#0' to right-template
        perform check-equation
      when 3
        move 1 to bind-count
        move '$ #0 @ Nat.zero @' to left-template
        move '#0' to right-template
        perform check-equation
        move 2 to bind-count
        move '$ #1 @ Nat.succ #0 @ @' to left-template
        move 'Nat.pred $ #1 @ #0 @ @' to right-template
        perform check-equation
      when 4
        move 1 to bind-count
        move '$ #0 @ Nat.zero @' to left-template
        move 'Nat.zero' to right-template
        perform check-equation
        move 2 to bind-count
        move '$ #1 @ Nat.succ #0 @ @' to left-template
        move 'Nat.add $ #1 @ #0 @ @ #1 @' to right-template
        perform check-equation
      when 5
        move 1 to bind-count
        move '$ #0 @ Nat.zero @' to left-template
        move 'Nat.succ Nat.zero @' to right-template
        perform check-equation
        move 2 to bind-count
        move '$ #1 @ Nat.succ #0 @ @' to left-template
        move 'Nat.mul $ #1 @ #0 @ @ #1 @' to right-template
        perform check-equation
      when 6
        move 0 to bind-count
        move '$ Nat.zero @ Nat.zero @' to left-template
        move 'Bool.true' to right-template
        perform check-equation
        move 1 to bind-count
        move '$ Nat.zero @ Nat.succ #0 @ @' to left-template
        move 'Bool.false' to right-template
        perform check-equation
        move 1 to bind-count
        move '$ Nat.succ #0 @ @ Nat.zero @' to left-template
        move 'Bool.false' to right-template
        perform check-equation
        move 2 to bind-count
        move '$ Nat.succ #1 @ @ Nat.succ #0 @ @' to left-template
        move '$ #1 @ #0 @' to right-template
        perform check-equation
      when 7
        move 0 to bind-count
        move '$ Nat.zero @ Nat.zero @' to left-template
        move 'Bool.true' to right-template
        perform check-equation
        move 1 to bind-count
        move '$ Nat.zero @ Nat.succ #0 @ @' to left-template
        move 'Bool.true' to right-template
        perform check-equation
        move 1 to bind-count
        move '$ Nat.succ #0 @ @ Nat.zero @' to left-template
        move 'Bool.false' to right-template
        perform check-equation
        move 2 to bind-count
        move '$ Nat.succ #1 @ @ Nat.succ #0 @ @' to left-template
        move '$ #1 @ #0 @' to right-template
        perform check-equation
      when 8
        move 1 to bind-count
        move '$ #0 @ Nat.zero @' to left-template
        move '#0' to right-template
        perform check-equation
        move 2 to bind-count
        move '$ #0 @ Nat.succ #1 @ @' to left-template
        move '$ Nat.mul Nat.succ Nat.succ Nat.zero @ @ @ #0 @ @ #1 @' to right-template
        perform check-equation
      when 9
        move 1 to bind-count
        move '$ #0 @ Nat.zero @' to left-template
        move '#0' to right-template
        perform check-equation
        move 2 to bind-count
        move '$ #0 @ Nat.succ #1 @ @' to left-template
        move 'Nat.div $ #0 @ #1 @ @ Nat.succ Nat.succ Nat.zero @ @ @' to right-template
        perform check-equation
      when 10
        *> The bitwise wrapper must be syntactically an application.
        set address of expr-arena to expr-ptr
        if expr-kind(body-id) not = 3 move 1 to verdict goback end-if
        move expr-a(body-id) to tmp
        if expr-kind(tmp) not = 2 or expr-b(tmp) not = 0
            move 1 to verdict goback
        end-if
        move expr-a(tmp) to name-id
        call 'name-matches' using kernel-state name-id 'Nat.bitwise' matched
        if matched = 0 move 1 to verdict goback end-if
        move expr-b(body-id) to body-id
        move 1 to bind-count
        move '$ Bool.false @ #0 @' to left-template
        move 'Bool.false' to right-template
        perform check-equation
        move 1 to bind-count
        move '$ Bool.true @ #0 @' to left-template
        move '#0' to right-template
        perform check-equation
      when 11
        *> The bitwise wrapper must be syntactically an application.
        set address of expr-arena to expr-ptr
        if expr-kind(body-id) not = 3 move 1 to verdict goback end-if
        move expr-a(body-id) to tmp
        if expr-kind(tmp) not = 2 or expr-b(tmp) not = 0
            move 1 to verdict goback
        end-if
        move expr-a(tmp) to name-id
        call 'name-matches' using kernel-state name-id 'Nat.bitwise' matched
        if matched = 0 move 1 to verdict goback end-if
        move expr-b(body-id) to body-id
        move 1 to bind-count
        move '$ Bool.false @ #0 @' to left-template
        move '#0' to right-template
        perform check-equation
        move 1 to bind-count
        move '$ Bool.true @ #0 @' to left-template
        move 'Bool.true' to right-template
        perform check-equation
      when 12
        *> The bitwise wrapper must be syntactically an application.
        set address of expr-arena to expr-ptr
        if expr-kind(body-id) not = 3 move 1 to verdict goback end-if
        move expr-a(body-id) to tmp
        if expr-kind(tmp) not = 2 or expr-b(tmp) not = 0
            move 1 to verdict goback
        end-if
        move expr-a(tmp) to name-id
        call 'name-matches' using kernel-state name-id 'Nat.bitwise' matched
        if matched = 0 move 1 to verdict goback end-if
        move expr-b(body-id) to body-id
        move 0 to bind-count
        move '$ Bool.false @ Bool.false @' to left-template
        move 'Bool.false' to right-template
        perform check-equation
        move 0 to bind-count
        move '$ Bool.true @ Bool.false @' to left-template
        move 'Bool.true' to right-template
        perform check-equation
        move 0 to bind-count
        move '$ Bool.false @ Bool.true @' to left-template
        move 'Bool.true' to right-template
        perform check-equation
        move 0 to bind-count
        move '$ Bool.true @ Bool.true @' to left-template
        move 'Bool.false' to right-template
        perform check-equation
      when 13
        call 'primitive-template' using kernel-state body-id 'Char' tmp
        call 'infer-sort' using kernel-state tmp depth-val k
      when 14
        call 'primitive-template' using kernel-state body-id 'Char' tmp
        call 'infer-sort' using kernel-state tmp depth-val k
        call 'primitive-template' using kernel-state body-id 'List.0 Char @' tmp
        call 'infer-sort' using kernel-state tmp depth-val k
        move 'List.nil.0 Char @' to left-template
        move 'List.0 Char @' to right-template
        perform check-inferred
        move 'List.cons.0 Char @' to left-template
        move 'Char List.0 Char @ List.0 Char @ > >' to right-template
        perform check-inferred
    end-evaluate
    goback.
require-constant.
    call 'builtin-name' using kernel-state spelling tmp
    if verdict not = 0 exit paragraph end-if
    set address of name-arena to name-ptr
    if name-env(tmp) = 0 move 1 to verdict end-if.
check-inferred.
    if verdict not = 0 exit paragraph end-if
    call 'primitive-template' using kernel-state body-id left-template tmp
    call 'infer-type' using kernel-state tmp depth-val left-expr
    call 'primitive-template' using kernel-state body-id right-template right-expr
    call 'def-equal' using kernel-state left-expr right-expr depth-val answer
    if verdict = 0 and answer = 0 move 1 to verdict end-if.
check-equation.
    if verdict not = 0 exit paragraph end-if
    call 'primitive-template' using kernel-state body-id left-template left-expr
    call 'primitive-template' using kernel-state body-id right-template right-expr
    perform bind-count times
        call 'expr-intern' using kernel-state pi-kind nat-type left-expr zero-val zero-val tmp
        move tmp to left-expr
        call 'expr-intern' using kernel-state pi-kind nat-type right-expr zero-val zero-val tmp
        move tmp to right-expr
    end-perform
    call 'def-equal' using kernel-state left-expr right-expr depth-val answer
    if verdict = 0 and answer = 0 move 1 to verdict end-if
    if verdict not = 0
        accept trace-option from environment 'LEAN4COBOL_TRACE'
            on exception move space to trace-option
        end-accept
        if trace-option = '1'
            display 'primitive equation failed (' bind-count ' binders): '
                function trim(left-template) ' = ' function trim(right-template) upon syserr
        end-if
    end-if.
end program check-primitive-definition.

*> Small postfix notation for closed, kernel-owned expression quotations.
*> $ is the candidate body, #0/#1 are bound variables, @ is application,
*> > is forall; .0 and .1 suffixes denote universe lists [0] and [1].
*> No export content is interpreted here. Invalid templates are internal errors.
identification division.
program-id. primitive-template.
data division.
local-storage section.
01 source-text pic x(512).
01 token-text pic x(64).
01 scan-pos binary-long unsigned value 1.
01 token-length binary-long unsigned.
01 stack-size binary-long unsigned.
01 expression-stack.
   02 stack-item binary-long unsigned occurs 32.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 result-id binary-long unsigned.
01 levels binary-long unsigned.
01 one-level binary-long unsigned.
01 one-val binary-long unsigned value 1.
01 zero-val binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 body-id binary-long unsigned.
01 template-text pic x any length.
01 result-expr binary-long unsigned.
procedure division using kernel-state body-id template-text result-expr.
    move 0 to result-expr
    if verdict not = 0 goback end-if
    move template-text to source-text
    perform until scan-pos > function length(function trim(source-text)) or verdict not = 0
        move spaces to token-text
        unstring source-text delimited by all space into token-text with pointer scan-pos end-unstring
        move 0 to a b levels
        evaluate token-text
          when '@' when '>'
            if stack-size < 2 move 3 to verdict goback end-if
            move stack-item(stack-size) to b subtract 1 from stack-size
            move stack-item(stack-size) to a subtract 1 from stack-size
            if token-text = '@' move 3 to k else move 5 to k end-if
          when '#0' move 0 to k a
          when '#1' move 0 to k move 1 to a
          when '$' move body-id to result-id move 99 to k
          when other
            move function length(function trim(token-text)) to token-length
            if token-length > 2
                if token-text(token-length - 1:2) = '.1' or '.0'
                    move one-val to one-level
                    if token-text(token-length - 1:2) = '.1'
                        call 'level-intern' using kernel-state one-val one-val zero-val one-level
                    end-if
                    move spaces to token-text(token-length - 1:2)
                    call 'list-intern' using kernel-state one-level zero-val levels
                end-if
            end-if
            call 'builtin-name' using kernel-state token-text a
            move levels to b move 2 to k
        end-evaluate
        if k not = 99
            call 'expr-intern' using kernel-state k a b zero-val zero-val result-id
        end-if
        if stack-size = 32 move 3 to verdict goback end-if
        add 1 to stack-size move result-id to stack-item(stack-size)
    end-perform
    if verdict not = 0 goback end-if
    if stack-size not = 1 move 3 to verdict goback end-if
    move stack-item(1) to result-expr
    goback.
end program primitive-template.
