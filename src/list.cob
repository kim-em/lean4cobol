identification division.
program-id. list-intern.
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
linkage section.
copy 'state.cpy'.
01 arg-a binary-long unsigned.
01 arg-b binary-long unsigned.
01 result-id binary-long unsigned.
copy 'list.cpy'.
procedure division using kernel-state arg-a arg-b result-id.
    move 0 to result-id
    if verdict not = 0 goback end-if
    move 0 to hash-acc
    move arg-a to hash-input perform hash-mix
    move arg-b to hash-input perform hash-mix
    move hash-acc to h
    move list-hcap to half-cap
    divide 2 into half-cap
    if list-count >= half-cap
        set old-hptr to list-hptr
        compute wanted = function max(32, list-hcap * 2)
        move 0 to list-hcap
        set list-hptr to null
        move 4 to width
        call 'arena-reserve' using list-hptr list-hcap wanted
            width verdict
        if verdict not = 0
            set list-hptr to old-hptr goback
        end-if
        set address of list-htable to list-hptr
        set address of list-arena to list-ptr
        perform varying i from 1 by 1 until i > list-count
            move list-hash(i) to slot-id
            move slot-id to slot-quot
            divide list-hcap into slot-quot
            multiply list-hcap by slot-quot
            subtract slot-quot from slot-id
            add 1 to slot-id
            perform until list-slot(slot-id) = 0
                add 1 to slot-id
                if slot-id > list-hcap move 1 to slot-id end-if
            end-perform
            move i to list-slot(slot-id)
        end-perform
        if old-hptr not = null call 'arena-release' using old-hptr end-if
    end-if
    set address of list-htable to list-hptr
    set address of list-arena to list-ptr
    move h to slot-id
    move slot-id to slot-quot
    divide list-hcap into slot-quot
    multiply list-hcap by slot-quot
    subtract slot-quot from slot-id
    add 1 to slot-id
    perform until list-slot(slot-id) = 0
        move list-slot(slot-id) to node-id
        if list-a(node-id) = arg-a and list-b(node-id) = arg-b
            move node-id to result-id goback
        end-if
        add 1 to slot-id
        if slot-id > list-hcap move 1 to slot-id end-if
    end-perform
    move list-count to wanted
    add 1 to wanted
    move length of list-node to width
    call 'arena-reserve' using list-ptr list-cap wanted width
        verdict
    if verdict not = 0 goback end-if
    set address of list-arena to list-ptr
    add 1 to list-count
    move list-count to result-id list-slot(slot-id)
    move arg-a to list-a(result-id)
    move arg-b to list-b(result-id)
    move h to list-hash(result-id)
    move 1 to list-length(result-id)
    if arg-b not = 0
        add list-length(arg-b) to list-length(result-id)
    end-if
    goback.
copy 'hash-mix.cpy'.
end program list-intern.

identification division.
program-id. list-reverse.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 head-id binary-long unsigned.
01 acc binary-long unsigned.
01 next-id binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'list.cpy'.
01 input-list binary-long unsigned.
01 result-list binary-long unsigned.
procedure division using kernel-state input-list result-list.
    move input-list to current-id
    perform until current-id = 0 or verdict not = 0
        set address of list-arena to list-ptr
        move list-a(current-id) to head-id move list-b(current-id) to current-id
        call 'list-intern' using kernel-state head-id acc next-id
        move next-id to acc
    end-perform
    move acc to result-list
    goback.
end program list-reverse.

identification division.
program-id. list-append.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 head-id binary-long unsigned.
01 acc binary-long unsigned.
01 next-id binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'list.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 result-list binary-long unsigned.
procedure division using kernel-state lhs rhs result-list.
    move rhs to acc
    call 'list-reverse' using kernel-state lhs current-id
    perform until current-id = 0 or verdict not = 0
        set address of list-arena to list-ptr
        move list-a(current-id) to head-id move list-b(current-id) to current-id
        call 'list-intern' using kernel-state head-id acc next-id
        move next-id to acc
    end-perform
    move acc to result-list
    goback.
end program list-append.

identification division.
program-id. list-nth.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 i binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'list.cpy'.
01 input-list binary-long unsigned.
01 index-val binary-long unsigned.
01 result-id binary-long unsigned.
procedure division using kernel-state input-list index-val result-id.
    move input-list to current-id move 0 to result-id
    if verdict not = 0 goback end-if
    set address of list-arena to list-ptr
    perform varying i from 0 by 1 until i >= index-val or current-id = 0
        move list-b(current-id) to current-id
    end-perform
    if current-id not = 0 move list-a(current-id) to result-id end-if
    goback.
end program list-nth.

identification division.
program-id. list-slice.
data division.
local-storage section.
01 p binary-long unsigned.
01 acc binary-long unsigned.
01 a binary-long unsigned.
01 tmp binary-long unsigned.
01 i binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'list.cpy'.
01 input-list binary-long unsigned.
01 start-index binary-long unsigned.
01 count-val binary-long unsigned.
01 result-list binary-long unsigned.
procedure division using kernel-state input-list start-index count-val result-list.
    move input-list to p
    if verdict not = 0 goback end-if
    set address of list-arena to list-ptr
    perform varying i from 0 by 1 until i >= start-index or p = 0
        move list-b(p) to p
    end-perform
    perform varying i from 0 by 1 until i >= count-val or p = 0 or verdict not = 0
        set address of list-arena to list-ptr
        move list-a(p) to a move list-b(p) to p
        call 'list-intern' using kernel-state a acc tmp move tmp to acc
    end-perform
    call 'list-reverse' using kernel-state acc result-list
    goback.
end program list-slice.

*> Ordinary declaration checks retain only their original exported terms.
*> Remove transient cells in reverse insertion order. Rehashing inserts in
*> ascending ID order, so clearing these slots cannot break an older probe.
identification division.
program-id. list-rewind.
data division.
local-storage section.
01 slot-id usage index.
01 slot-quot usage index.
linkage section.
copy 'state.cpy'.
copy 'list.cpy'.
01 saved-count binary-long unsigned.
procedure division using kernel-state saved-count.
    set address of list-arena to list-ptr
    set address of list-htable to list-hptr
    perform until list-count <= saved-count
        move list-hash(list-count) to slot-id
        move slot-id to slot-quot
        divide list-hcap into slot-quot
        multiply list-hcap by slot-quot
        subtract slot-quot from slot-id
        add 1 to slot-id
        perform until list-slot(slot-id) = list-count
            add 1 to slot-id
            if slot-id > list-hcap move 1 to slot-id end-if
        end-perform
        move 0 to list-slot(slot-id)
        initialize list-node(list-count)
        subtract 1 from list-count
    end-perform
    goback.
end program list-rewind.
