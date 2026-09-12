*> COBOL port of Lean4Lean/Level.lean (Mario Carneiro), Apache-2.0.
*> Modified representation: normal forms store individual C/V sublevels;
*> comparison discharges each sublevel independently, as NormLevel.le does.
identification division.
program-id. level-intern.
data division.
local-storage section.
01 mod-input binary-double unsigned.
01 mod-quotient binary-double unsigned.
01 h binary-double unsigned.
01 slot-id binary-long unsigned.
01 node-id binary-long unsigned.
01 i binary-long unsigned.
01 wanted binary-long unsigned.
01 width binary-long unsigned.
01 old-hptr usage pointer.
linkage section.
copy 'state.cpy'.
01 kind-id binary-long unsigned.
01 arg-a binary-long unsigned.
01 arg-b binary-long unsigned.
01 result-id binary-long unsigned.
copy 'levels.cpy'.
procedure division using kernel-state kind-id arg-a arg-b result-id.
    move 0 to result-id
    if verdict not = 0 goback end-if
    if kind-id > 4
        move 3 to verdict goback
    end-if
    compute mod-input = (kind-id * 65599 + arg-a) *
        65599 + arg-b
    divide mod-input by 4294967291 giving mod-quotient
        remainder h
    if level-count * 2 >= level-hcap
        set old-hptr to level-hptr
        compute wanted = function max(32, level-hcap * 2)
        move 0 to level-hcap
        set level-hptr to null
        move 4 to width
        call 'arena-reserve' using level-hptr level-hcap wanted
            width verdict
        if verdict not = 0
            set level-hptr to old-hptr goback
        end-if
        set address of level-htable to level-hptr
        set address of level-arena to level-ptr
        perform varying i from 1 by 1 until i > level-count
            compute mod-input = level-hash(i)
            divide mod-input by level-hcap giving mod-quotient
                remainder slot-id
    add 1 to slot-id
            perform until level-slot(slot-id) = 0
                add 1 to slot-id
                if slot-id > level-hcap move 1 to slot-id end-if
            end-perform
            move i to level-slot(slot-id)
        end-perform
        if old-hptr not = null call 'arena-release' using old-hptr end-if
    end-if
    set address of level-htable to level-hptr
    set address of level-arena to level-ptr
    compute mod-input = h
    divide mod-input by level-hcap giving mod-quotient
        remainder slot-id
    add 1 to slot-id
    perform until level-slot(slot-id) = 0
        move level-slot(slot-id) to node-id
        if level-kind(node-id) = kind-id and
            level-a(node-id) = arg-a and level-b(node-id) = arg-b
            move node-id to result-id goback
        end-if
        add 1 to slot-id
        if slot-id > level-hcap move 1 to slot-id end-if
    end-perform
    move level-count to wanted
    add 1 to wanted
    move length of level-node to width
    call 'arena-reserve' using level-ptr level-cap wanted width
        verdict
    if verdict not = 0 goback end-if
    set address of level-arena to level-ptr
    add 1 to level-count
    move level-count to result-id level-slot(slot-id)
    move kind-id to level-kind(result-id)
    move arg-a to level-a(result-id)
    move arg-b to level-b(result-id)
    move h to level-hash(result-id)
    move result-id to level-base(result-id)
    evaluate kind-id
      when 0 move 1 to level-always-zero(result-id)
      when 1
        move level-has-param(arg-a) to level-has-param(result-id)
        move 1 to level-never-zero(result-id)
        compute level-offset(result-id) = level-offset(arg-a) + 1
        move level-base(arg-a) to level-base(result-id)
      when 2 when 3
        compute level-has-param(result-id) = function max(
            level-has-param(arg-a), level-has-param(arg-b))
        if kind-id = 2
            compute level-always-zero(result-id) = function min(
                level-always-zero(arg-a), level-always-zero(arg-b))
            compute level-never-zero(result-id) = function max(
                level-never-zero(arg-a), level-never-zero(arg-b))
        else
            move level-never-zero(arg-b) to level-never-zero(result-id)
            move level-always-zero(arg-b) to level-always-zero(result-id)
        end-if
      when 4 move 1 to level-has-param(result-id)
    end-evaluate
    goback.
end program level-intern.

identification division.
program-id. level-normalize recursive.
data division.
local-storage section.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 ba binary-long unsigned.
01 bb binary-long unsigned.
01 k binary-long unsigned.
01 bk binary-long unsigned.
01 next-offset binary-long unsigned.
01 next-depth binary-long unsigned.
01 next-path binary-long unsigned.
01 walk-path binary-long unsigned.
01 new-level binary-long unsigned.
01 imax-kind binary-long unsigned value 3.
01 width binary-long unsigned.
01 wanted binary-long unsigned.
01 emit-var binary-long unsigned.
01 emit-path binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'normal.cpy'.
01 input-level binary-long unsigned.
01 conditions binary-long unsigned.
01 offset-val binary-long unsigned.
01 depth-val binary-long unsigned.
copy 'levels.cpy'.
procedure division using kernel-state norm-state input-level
    conditions offset-val depth-val.
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit or norm-fuel = 0
        move 2 to verdict goback
    end-if
    subtract 1 from norm-fuel
    move depth-val to next-depth
    add 1 to next-depth
    set address of level-arena to level-ptr
    move level-kind(input-level) to k
    move level-a(input-level) to a
    move level-b(input-level) to b
    move conditions to emit-path
    evaluate k
      when 0
        perform emit-constant
      when 1
        move offset-val to next-offset
        add 1 to next-offset
        call 'level-normalize' using kernel-state norm-state a
            conditions next-offset next-depth
      when 2
        call 'level-normalize' using kernel-state norm-state a
            conditions offset-val next-depth
        call 'level-normalize' using kernel-state norm-state b
            conditions offset-val next-depth
      when 3
        move level-kind(b) to bk
        move level-a(b) to ba
        move level-b(b) to bb
        evaluate bk
          when 0 perform emit-constant
          when 1
            call 'level-normalize' using kernel-state norm-state a
                conditions offset-val next-depth
            move offset-val to next-offset
            add 1 to next-offset
            call 'level-normalize' using kernel-state norm-state ba
                conditions next-offset next-depth
          when 2
            call 'level-intern' using kernel-state imax-kind a ba
                new-level
            call 'level-normalize' using kernel-state norm-state
                new-level conditions offset-val next-depth
            call 'level-intern' using kernel-state imax-kind a bb
                new-level
            call 'level-normalize' using kernel-state norm-state
                new-level conditions offset-val next-depth
          when 3
            call 'level-intern' using kernel-state imax-kind a bb
                new-level
            call 'level-normalize' using kernel-state norm-state
                new-level conditions offset-val next-depth
            call 'level-intern' using kernel-state imax-kind ba bb
                new-level
            call 'level-normalize' using kernel-state norm-state
                new-level conditions offset-val next-depth
          when 4
            move ba to emit-var
            perform parameter-node
            call 'level-normalize' using kernel-state norm-state a
                next-path offset-val next-depth
          when other move 3 to verdict
        end-evaluate
      when 4
        move a to emit-var
        perform parameter-node
      when other move 3 to verdict
    end-evaluate
    goback.
parameter-node.
    set address of path-arena to path-ptr
    move conditions to walk-path next-path
    perform until walk-path = 0
        if path-var(walk-path) = emit-var exit perform end-if
        move path-tail(walk-path) to walk-path
    end-perform
    if walk-path = 0
        perform emit-constant
        move path-count to wanted
        add 1 to wanted
        move length of path-node to width
        call 'arena-reserve' using path-ptr path-cap wanted width
            verdict
        if verdict not = 0 exit paragraph end-if
        set address of path-arena to path-ptr
        add 1 to path-count
        move path-count to next-path emit-path
        move emit-var to path-var(next-path)
        move conditions to path-tail(next-path)
        perform emit-variable
    else
        if offset-val not = 0 perform emit-variable end-if
    end-if.
emit-constant.
    if offset-val = 0 or
        (offset-val = 1 and emit-path not = 0)
        exit paragraph
    end-if
    perform reserve-term
    if verdict = 0 move 0 to term-var(term-count) end-if.
emit-variable.
    perform reserve-term
    if verdict = 0 move emit-var to term-var(term-count) end-if.
reserve-term.
    move term-count to wanted
    add 1 to wanted
    move length of norm-term to width
    call 'arena-reserve' using term-ptr term-cap wanted width
        verdict
    if verdict not = 0 exit paragraph end-if
    set address of term-arena to term-ptr
    add 1 to term-count
    move emit-path to term-path(term-count)
    move offset-val to term-offset(term-count).
end program level-normalize.

identification division.
program-id. level-compare.
data division.
local-storage section.
copy 'normal-state.cpy'.
01 zero-val binary-long unsigned.
01 split-at binary-long unsigned.
01 first-term binary-long unsigned.
01 last-term binary-long unsigned.
01 other-first binary-long unsigned.
01 other-last binary-long unsigned.
01 i binary-long unsigned.
01 j binary-long unsigned.
01 p binary-long unsigned.
01 q binary-long unsigned.
01 dominated binary-char unsigned.
01 subset-ok binary-char unsigned.
01 swap-val binary-long unsigned.
01 direction-id binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'normal-tables.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
*> mode 0: equivalence, mode 1: lhs >= rhs.
01 compare-mode binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs compare-mode answer.
    move 0 to answer
    if verdict not = 0 goback end-if
    if lhs = rhs move 1 to answer goback end-if
    move 1000000 to norm-fuel
    call 'level-normalize' using kernel-state norm-state lhs
        zero-val zero-val zero-val
    move term-count to split-at
    call 'level-normalize' using kernel-state norm-state rhs
        zero-val zero-val zero-val
    if verdict = 0
        set address of term-arena to term-ptr
        set address of path-arena to path-ptr
        move split-at to first-term
        add 1 to first-term
        move term-count to last-term
        move 1 to other-first
        move split-at to other-last
        move 1 to answer
        perform compare-terms
        if compare-mode = 0 and answer = 1
            move first-term to swap-val
            move other-first to first-term
            move swap-val to other-first
            move last-term to swap-val
            move other-last to last-term
            move swap-val to other-last
            perform compare-terms
        end-if
    end-if
    if term-ptr not = null call 'arena-release' using term-ptr end-if
    if path-ptr not = null call 'arena-release' using path-ptr end-if
    goback.
compare-terms.
    perform varying i from first-term by 1 until i > last-term
        move 0 to dominated
        perform varying j from other-first by 1
            until j > other-last or dominated = 1
            if norm-fuel = 0
                move 2 to verdict move 0 to answer
                exit paragraph
            end-if
            subtract 1 from norm-fuel
            if (term-var(i) = 0 and
                ((term-var(j) = 0 and
                  term-offset(i) <= term-offset(j)) or
                 (term-var(j) not = 0 and
                  term-offset(i) <= term-offset(j) + 1))) or
               (term-var(i) not = 0 and
                term-var(i) = term-var(j) and
                term-offset(i) <= term-offset(j))
                perform check-subset
                if subset-ok = 1 move 1 to dominated end-if
            end-if
        end-perform
        if dominated = 0 move 0 to answer exit paragraph end-if
    end-perform.
check-subset.
    move 1 to subset-ok
    move term-path(j) to p
    perform until p = 0
        move term-path(i) to q
        perform until q = 0
            if path-var(p) = path-var(q) exit perform end-if
            move path-tail(q) to q
        end-perform
        if q = 0 move 0 to subset-ok exit paragraph end-if
        move path-tail(p) to p
    end-perform.
end program level-compare.

*> Lean.mkLevelMax'/mkLevelIMax': cheap constructor simplification used
*> by substitution and the type checker. Raw parsing still uses level-intern.
identification division.
program-id. level-make.
data division.
local-storage section.
01 k binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'levels.cpy'.
01 kind-id binary-long unsigned.
01 arg-a binary-long unsigned.
01 arg-b binary-long unsigned.
01 result-id binary-long unsigned.
procedure division using kernel-state kind-id arg-a arg-b result-id.
    move 0 to result-id
    if verdict not = 0 goback end-if
    move kind-id to k
    set address of level-arena to level-ptr
    if k = 3
        evaluate true
          when level-never-zero(arg-b) = 1 move 2 to k
          when level-kind(arg-b) = 0 move arg-b to result-id goback
          when level-kind(arg-a) = 0 move arg-b to result-id goback
          when arg-a = arg-b move arg-a to result-id goback
        end-evaluate
    end-if
    if k = 2
        evaluate true
          when arg-a = arg-b move arg-a to result-id goback
          when level-kind(arg-a) = 0 move arg-b to result-id goback
          when level-kind(arg-b) = 0 move arg-a to result-id goback
          when level-kind(level-base(arg-b)) = 0 and
               level-offset(arg-a) >= level-offset(arg-b)
            move arg-a to result-id goback
          when level-kind(arg-a) = 2 and
               (arg-b = level-a(arg-a) or arg-b = level-b(arg-a))
            move arg-a to result-id goback
          when level-kind(level-base(arg-a)) = 0 and
               level-offset(arg-b) >= level-offset(arg-a)
            move arg-b to result-id goback
          when level-kind(arg-b) = 2 and
               (arg-a = level-a(arg-b) or arg-a = level-b(arg-b))
            move arg-b to result-id goback
          when level-base(arg-a) = level-base(arg-b)
            if level-offset(arg-a) >= level-offset(arg-b)
                move arg-a to result-id
            else move arg-b to result-id end-if
            goback
        end-evaluate
    end-if
    call 'level-intern' using kernel-state k arg-a arg-b result-id
    goback.
end program level-make.
