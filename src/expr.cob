identification division.
program-id. expr-intern.
data division.
local-storage section.
01 half-cap usage index.
copy 'hash-native.cpy'.
01 h binary-double unsigned.
01 slot-id usage index.
01 slot-quot usage index.
01 node-id binary-long unsigned.
01 i binary-long unsigned.
01 wanted binary-long unsigned.
01 width binary-long unsigned.
01 old-hptr usage pointer.
01 child-id binary-long unsigned.
01 body-range binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 kind-id binary-long unsigned.
01 arg-a binary-long unsigned.
01 arg-b binary-long unsigned.
01 arg-c binary-long unsigned.
01 arg-d binary-long unsigned.
01 result-id binary-long unsigned.
copy 'expr.cpy'.
copy 'levels.cpy'.
copy 'list.cpy'.
procedure division using kernel-state kind-id arg-a arg-b
    arg-c arg-d result-id.
    move 0 to result-id
    if verdict not = 0 goback end-if
    if kind-id > 11
        move 3 to verdict goback
    end-if
    move kind-id to hash-acc
    move arg-a to hash-input perform hash-mix
    move arg-b to hash-input perform hash-mix
    move arg-c to hash-input perform hash-mix
    move arg-d to hash-input perform hash-mix
    move hash-acc to h
    move expr-hcap to half-cap
    divide 2 into half-cap
    if expr-count >= half-cap
        set old-hptr to expr-hptr
        compute wanted = function max(32, expr-hcap * 2)
        move 0 to expr-hcap
        set expr-hptr to null
        move 4 to width
        call 'arena-reserve' using expr-hptr expr-hcap wanted
            width verdict
        if verdict not = 0
            set expr-hptr to old-hptr goback
        end-if
        set address of expr-htable to expr-hptr
        set address of expr-arena to expr-ptr
        perform varying i from 1 by 1 until i > expr-count
            move expr-hash(i) to slot-id
            move slot-id to slot-quot
            divide expr-hcap into slot-quot
            multiply expr-hcap by slot-quot
            subtract slot-quot from slot-id
            add 1 to slot-id
            perform until expr-slot(slot-id) = 0
                add 1 to slot-id
                if slot-id > expr-hcap move 1 to slot-id end-if
            end-perform
            move i to expr-slot(slot-id)
        end-perform
        if old-hptr not = null call 'arena-release' using old-hptr end-if
    end-if
    set address of expr-htable to expr-hptr
    set address of expr-arena to expr-ptr
    move h to slot-id
    move slot-id to slot-quot
    divide expr-hcap into slot-quot
    multiply expr-hcap by slot-quot
    subtract slot-quot from slot-id
    add 1 to slot-id
    perform until expr-slot(slot-id) = 0
        move expr-slot(slot-id) to node-id
        if expr-kind(node-id) = kind-id and
            expr-a(node-id) = arg-a and expr-b(node-id) = arg-b and
            expr-c(node-id) = arg-c and expr-d(node-id) = arg-d
            move node-id to result-id goback
        end-if
        add 1 to slot-id
        if slot-id > expr-hcap move 1 to slot-id end-if
    end-perform
    move expr-count to wanted
    add 1 to wanted
    move length of expr-node to width
    call 'arena-reserve' using expr-ptr expr-cap wanted width
        verdict
    if verdict not = 0 goback end-if
    set address of expr-arena to expr-ptr
    add 1 to expr-count
    move expr-count to result-id expr-slot(slot-id)
    move kind-id to expr-kind(result-id)
    move arg-a to expr-a(result-id)
    move arg-b to expr-b(result-id)
    move arg-c to expr-c(result-id)
    move arg-d to expr-d(result-id)
    move h to expr-hash(result-id)
    perform cache-metadata
    goback.
cache-metadata.
    evaluate kind-id
      when 0
        if arg-a = 4294967295 move 2 to verdict exit paragraph end-if
        compute expr-lbvr(result-id) = arg-a + 1
      when 1
        set address of level-arena to level-ptr
        move level-has-param(arg-a) to expr-has-param(result-id)
      when 2
        set address of list-arena to list-ptr
        set address of level-arena to level-ptr
        move arg-b to i
        perform until i = 0
            if level-has-param(list-a(i)) = 1
                move 1 to expr-has-param(result-id)
                exit perform
            end-if
            move list-b(i) to i
        end-perform
      when 3
        move arg-a to child-id perform merge-child
        move arg-b to child-id perform merge-child
      when 4 when 5
        move arg-b to child-id perform merge-child
        if expr-lbvr(result-id) > 0
            subtract 1 from expr-lbvr(result-id)
        end-if
        move arg-a to child-id perform merge-child
      when 6
        move arg-c to child-id perform merge-child
        if expr-lbvr(result-id) > 0
            subtract 1 from expr-lbvr(result-id)
        end-if
        move arg-a to child-id perform merge-child
        move arg-b to child-id perform merge-child
      when 7 move arg-c to child-id perform merge-child
      when 9 move 1 to expr-has-string(result-id)
      when 10 move 1 to expr-has-fvar(result-id)
      when 11 move arg-a to child-id perform merge-child
    end-evaluate.
merge-child.
    if expr-lbvr(child-id) > expr-lbvr(result-id)
        move expr-lbvr(child-id) to expr-lbvr(result-id)
    end-if
    if expr-has-fvar(child-id) > expr-has-fvar(result-id)
        move expr-has-fvar(child-id) to expr-has-fvar(result-id)
    end-if
    if expr-has-param(child-id) > expr-has-param(result-id)
        move expr-has-param(child-id) to expr-has-param(result-id)
    end-if
    if expr-has-string(child-id) > expr-has-string(result-id)
        move expr-has-string(child-id) to expr-has-string(result-id)
    end-if.
copy 'hash-mix.cpy'.
end program expr-intern.

*> Ordinary declaration checks retain only their original exported terms.
*> Remove transient cells in reverse insertion order. Rehashing inserts in
*> ascending ID order, so clearing these slots cannot break an older probe.
identification division.
program-id. expr-rewind.
data division.
local-storage section.
01 slot-id usage index.
01 slot-quot usage index.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 saved-count binary-long unsigned.
procedure division using kernel-state saved-count.
    set address of expr-arena to expr-ptr
    set address of expr-htable to expr-hptr
    perform until expr-count <= saved-count
        move expr-hash(expr-count) to slot-id
        move slot-id to slot-quot
        divide expr-hcap into slot-quot
        multiply expr-hcap by slot-quot
        subtract slot-quot from slot-id
        add 1 to slot-id
        perform until expr-slot(slot-id) = expr-count
            add 1 to slot-id
            if slot-id > expr-hcap move 1 to slot-id end-if
        end-perform
        move 0 to expr-slot(slot-id)
        initialize expr-node(expr-count)
        subtract 1 from expr-count
    end-perform
    goback.
end program expr-rewind.
