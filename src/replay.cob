*> Lean4Lean/Replay.lean: dependency replay is distinct from type checking.
*> Exported metadata remains in name-decl; name-env contains checked/generated
*> constants only. Constructors and recursors are compared after replay.
identification division.
program-id. replay-run.
data division.
local-storage section.
01 i binary-long unsigned.
01 n binary-long unsigned.
01 zero-val binary-long unsigned.
01 matched binary-char unsigned.
01 progress-option pic x.
01 next-progress binary-long unsigned value 1000.
linkage section.
copy 'state.cpy'.
copy 'declarations.cpy'.
procedure division using kernel-state.
    accept progress-option from environment 'LEAN4COBOL_PROGRESS'
        on exception move space to progress-option
    end-accept
    move decl-count to export-count
    perform varying i from 1 by 1 until i > export-count or verdict not = 0
        set address of decl-arena to decl-ptr
        if decl-unsafe(i) = 1
            move 3 to decl-replay(i) decl-status(i)
        end-if
        move decl-name(i) to n
        *> Main.lean erases these names regardless of the exported kind.
        call 'name-matches' using kernel-state n 'Quot.mk' matched
        if matched = 0 call 'name-matches' using kernel-state n 'Quot.lift' matched end-if
        if matched = 0 call 'name-matches' using kernel-state n 'Quot.ind' matched end-if
        if matched = 1 move 3 to decl-replay(i) end-if
    end-perform
    perform varying i from 1 by 1 until i > export-count or verdict not = 0
        call 'replay-constant' using kernel-state i zero-val
        if progress-option = '1' and i >= next-progress
            display 'replayed export=' i '/' export-count
                ' checked=' checked-count ' exprs=' expr-count upon syserr
            add 1000 to next-progress
        end-if
    end-perform
    perform varying i from 1 by 1 until i > export-count or verdict not = 0
        set address of decl-arena to decl-ptr
        if decl-replay(i) = 2 and (decl-kind(i) = 5 or decl-kind(i) = 6)
            call 'replay-compare' using kernel-state i
            if verdict not = 0 call 'replay-diagnostic' using kernel-state i end-if
        end-if
    end-perform
    goback.
end program replay-run.

identification division.
program-id. replay-name recursive.
data division.
local-storage section.
01 declaration-id binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'names.cpy'.
01 name-id binary-long unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state name-id depth-val.
    if verdict not = 0 goback end-if
    set address of name-arena to name-ptr
    move name-decl(name-id) to declaration-id
    if declaration-id not = 0
        call 'replay-constant' using kernel-state declaration-id depth-val
    end-if
    goback.
end program replay-name.

identification division.
program-id. replay-constant recursive.
data division.
local-storage section.
01 ty binary-long unsigned.
01 val binary-long unsigned.
01 kind-id binary-long unsigned.
01 names-list binary-long unsigned.
01 name-id binary-long unsigned.
01 next-depth binary-long unsigned.
01 stamp binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'declarations.cpy'.
copy 'expr.cpy'.
copy 'list.cpy'.
01 declaration-id binary-long unsigned.
01 depth-val binary-long unsigned.
procedure division using kernel-state declaration-id depth-val.
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    set address of decl-arena to decl-ptr
    if decl-replay(declaration-id) not = 0 goback end-if
    move 1 to decl-replay(declaration-id)
    move decl-type(declaration-id) to ty move decl-value(declaration-id) to val
    move decl-kind(declaration-id) to kind-id
    evaluate kind-id
      when 4 move decl-ctors(declaration-id) to names-list
      when 6 move decl-all(declaration-id) to names-list
    end-evaluate
    move depth-val to next-depth
    add 1 to next-depth
    if replay-has-strings = 0
        set address of expr-arena to expr-ptr
        move expr-has-string(ty) to replay-has-strings
        if val not = 0 and replay-has-strings = 0
            move expr-has-string(val) to replay-has-strings
        end-if
        if replay-has-strings = 1
            call 'builtin-name' using kernel-state 'String.ofList' name-id
            call 'replay-name' using kernel-state name-id next-depth
            call 'builtin-name' using kernel-state 'Char.ofNat' name-id
            call 'replay-name' using kernel-state name-id next-depth
        end-if
    end-if
    add 1 to replay-stamp move replay-stamp to stamp
    call 'replay-expr' using kernel-state ty next-depth stamp
    if val not = 0 call 'replay-expr' using kernel-state val next-depth stamp end-if
    perform until names-list = 0 or verdict not = 0
        set address of list-arena to list-ptr
        move list-a(names-list) to name-id
        move list-b(names-list) to names-list
        call 'replay-name' using kernel-state name-id next-depth
    end-perform
    if verdict not = 0 goback end-if
    set address of decl-arena to decl-ptr
    if decl-replay(declaration-id) not = 1 goback end-if
    evaluate kind-id
      when 0 when 1 when 2 when 3
        call 'check-declaration' using kernel-state declaration-id next-depth
      when 4
        call 'check-inductive' using kernel-state declaration-id next-depth
      when 5 when 6 continue
      when 7
        call 'builtin-name' using kernel-state 'Eq' name-id
        call 'replay-name' using kernel-state name-id next-depth
        call 'initialize-quot' using kernel-state
    end-evaluate
    if verdict = 0
        set address of decl-arena to decl-ptr
        move 2 to decl-replay(declaration-id)
    else
        call 'replay-diagnostic' using kernel-state declaration-id
    end-if
    goback.
end program replay-constant.

*> Optional diagnostic identifies the declaration where replay first failed.
identification division.
program-id. replay-diagnostic.
data division.
local-storage section.
01 trace-option pic x.
linkage section.
copy 'state.cpy'.
01 declaration-id binary-long unsigned.
procedure division using kernel-state declaration-id.
    accept trace-option from environment 'LEAN4COBOL_TRACE'
        on exception move space to trace-option
    end-accept
    if trace-option = '1'
        display 'replay failed: export declaration=' declaration-id ' verdict=' verdict
            ' method-depth=' tc-method-depth upon syserr
    end-if
    goback.
end program replay-diagnostic.

identification division.
program-id. replay-expr recursive.
data division.
local-storage section.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 body-id binary-long unsigned.
01 next-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 stamp binary-long unsigned.
procedure division using kernel-state input-expr depth-val stamp.
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    set address of expr-arena to expr-ptr
    if expr-replay-stamp(input-expr) = stamp goback end-if
    move stamp to expr-replay-stamp(input-expr)
    move expr-kind(input-expr) to k
    move expr-a(input-expr) to a move expr-b(input-expr) to b move expr-c(input-expr) to body-id
    move depth-val to next-depth
    add 1 to next-depth
    evaluate k
      when 2 call 'replay-name' using kernel-state a next-depth
      when 3 when 4 when 5 when 6
        call 'replay-expr' using kernel-state a next-depth stamp
        call 'replay-expr' using kernel-state b next-depth stamp
        if k = 6 call 'replay-expr' using kernel-state body-id next-depth stamp end-if
      when 7 call 'replay-expr' using kernel-state body-id next-depth stamp
      when 11 call 'replay-expr' using kernel-state a next-depth stamp
    end-evaluate
    goback.
end program replay-expr.

identification division.
program-id. replay-compare.
data division.
local-storage section.
01 name-id binary-long unsigned.
01 actual-id binary-long unsigned.
01 p binary-long unsigned.
01 q binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
copy 'list.cpy'.
01 declaration-id binary-long unsigned.
procedure division using kernel-state declaration-id.
    if verdict not = 0 goback end-if
    set address of decl-arena to decl-ptr
    move decl-name(declaration-id) to name-id
    set address of name-arena to name-ptr
    move name-env(name-id) to actual-id
    if actual-id = 0 move 1 to verdict goback end-if
    if decl-kind(actual-id) not = decl-kind(declaration-id) or
       decl-name(actual-id) not = decl-name(declaration-id) or
       decl-params(actual-id) not = decl-params(declaration-id) or
       decl-type(actual-id) not = decl-type(declaration-id) or
       decl-num-params(actual-id) not = decl-num-params(declaration-id) or
       decl-unsafe(actual-id) not = decl-unsafe(declaration-id)
        move 1 to verdict goback
    end-if
    if decl-kind(declaration-id) = 5
        if decl-cidx(actual-id) not = decl-cidx(declaration-id) or
           decl-induct(actual-id) not = decl-induct(declaration-id) or
           decl-num-fields(actual-id) not = decl-num-fields(declaration-id)
            move 1 to verdict
        end-if
    else
        if decl-all(actual-id) not = decl-all(declaration-id) or
           decl-num-indices(actual-id) not = decl-num-indices(declaration-id) or
           decl-num-motives(actual-id) not = decl-num-motives(declaration-id) or
           decl-num-minors(actual-id) not = decl-num-minors(declaration-id) or
           decl-k(actual-id) not = decl-k(declaration-id)
            move 1 to verdict goback
        end-if
        move decl-rules(actual-id) to p move decl-rules(declaration-id) to q
        perform until p = 0 or q = 0
            set address of list-arena to list-ptr
            move list-a(p) to a move list-a(q) to b
            move list-b(p) to p move list-b(q) to q
            set address of rule-arena to rule-ptr
            if rule-node(a) not = rule-node(b) move 1 to verdict goback end-if
        end-perform
        if p not = q move 1 to verdict end-if
    end-if
    goback.
end program replay-compare.
