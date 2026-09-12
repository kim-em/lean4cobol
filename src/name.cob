identification division.
program-id. name-intern.
data division.
local-storage section.
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
01 prefix-id binary-long unsigned.
01 num binary-double unsigned.
01 name-text pic x any length.
01 text-length binary-long unsigned.
01 result-id binary-long unsigned.
copy 'names.cpy'.
procedure division using kernel-state kind-id prefix-id num
    name-text text-length result-id.
    move 0 to result-id
    if verdict not = 0 goback end-if
    if kind-id > 2 or prefix-id > name-count
        move 3 to verdict goback
    end-if
    compute h = function mod(kind-id * 65599 + prefix-id,
        4294967291)
    compute h = function mod(h * 65599 +
        function mod(num, 4294967291), 4294967291)
    if kind-id = 1
        perform varying i from 1 by 1 until i > text-length
            compute h = function mod(h * 257 +
                function ord(name-text(i:1)), 4294967291)
        end-perform
    end-if
    if name-count * 2 >= name-hcap
        set old-hptr to name-hptr
        compute wanted = function max(32, name-hcap * 2)
        move 0 to name-hcap
        set name-hptr to null
        move 4 to width
        call 'arena-reserve' using name-hptr name-hcap wanted
            width verdict
        if verdict not = 0
            set name-hptr to old-hptr goback
        end-if
        set address of name-htable to name-hptr
        set address of name-arena to name-ptr
        perform varying i from 1 by 1 until i > name-count
            compute slot-id = function mod(name-hash(i),
                name-hcap) + 1
            perform until name-slot(slot-id) = 0
                add 1 to slot-id
                if slot-id > name-hcap move 1 to slot-id end-if
            end-perform
            move i to name-slot(slot-id)
        end-perform
        if old-hptr not = null call 'arena-release' using old-hptr end-if
    end-if
    set address of name-htable to name-hptr
    set address of name-arena to name-ptr
    set address of string-bytes to byte-ptr
    compute slot-id = function mod(h, name-hcap) + 1
    perform until name-slot(slot-id) = 0
        move name-slot(slot-id) to node-id
        if name-kind(node-id) = kind-id and
            name-pre(node-id) = prefix-id and
            name-number(node-id) = num and
            name-length(node-id) = text-length
            if text-length = 0
                move node-id to result-id goback
            end-if
            if string-bytes(name-start(node-id):text-length) =
                name-text(1:text-length)
                move node-id to result-id goback
            end-if
        end-if
        add 1 to slot-id
        if slot-id > name-hcap move 1 to slot-id end-if
    end-perform
    move name-count to wanted
    add 1 to wanted
    move length of name-node to width
    call 'arena-reserve' using name-ptr name-cap wanted width
        verdict
    if verdict not = 0 goback end-if
    set address of name-arena to name-ptr
    if text-length > 0
        move byte-count to wanted
        add text-length to wanted
        move 1 to width
        call 'arena-reserve' using byte-ptr byte-cap wanted width
            verdict
        if verdict not = 0 goback end-if
        set address of string-bytes to byte-ptr
    end-if
    add 1 to name-count
    move name-count to result-id name-slot(slot-id)
    move kind-id to name-kind(result-id)
    move prefix-id to name-pre(result-id)
    move num to name-number(result-id)
    move h to name-hash(result-id)
    move text-length to name-length(result-id)
    compute name-start(result-id) = byte-count + 1
    if text-length > 0
        move name-text(1:text-length) to
            string-bytes(byte-count + 1:text-length)
        add text-length to byte-count
    end-if
    goback.
end program name-intern.

*> Compare a name with a dotted builtin spelling without interning new names.
identification division.
program-id. name-matches.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 end-pos binary-long unsigned.
01 start-pos binary-long unsigned.
01 part-size binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'names.cpy'.
01 input-name binary-long unsigned.
01 text-val pic x any length.
01 answer binary-char unsigned.
procedure division using kernel-state input-name text-val answer.
    move 0 to answer
    if verdict not = 0 goback end-if
    move input-name to current-id
    compute end-pos = function length(function trim(text-val trailing))
    set address of name-arena to name-ptr
    set address of string-bytes to byte-ptr
    perform until end-pos = 0
        if current-id = 0 goback end-if
        if name-kind(current-id) not = 1 goback end-if
        move end-pos to start-pos
        perform until start-pos = 0
            if text-val(start-pos:1) = '.' exit perform end-if
            subtract 1 from start-pos
        end-perform
        move end-pos to part-size
        subtract start-pos from part-size
        if name-length(current-id) not = part-size goback end-if
        add 1 to start-pos
        if string-bytes(name-start(current-id):part-size) not = text-val(start-pos:part-size) goback end-if
        move name-pre(current-id) to current-id
        if start-pos = 1 move 0 to end-pos else compute end-pos = start-pos - 2 end-if
    end-perform
    if current-id = 1 move 1 to answer end-if
    goback.
end program name-matches.

identification division.
program-id. builtin-name.
data division.
local-storage section.
01 spelling pic x(256).
01 current-id binary-long unsigned value 1.
01 next-id binary-long unsigned.
01 start-pos binary-long unsigned value 1.
01 end-pos binary-long unsigned.
01 text-size binary-long unsigned.
01 part-size binary-long unsigned.
01 kind-id binary-long unsigned value 1.
01 number-val binary-double unsigned.
linkage section.
copy 'state.cpy'.
01 text-val pic x any length.
01 result-id binary-long unsigned.
procedure division using kernel-state text-val result-id.
    move text-val to spelling
    compute text-size = function length(function trim(spelling trailing))
    perform until start-pos > text-size or verdict not = 0
        move start-pos to end-pos
        perform until end-pos > text-size
            if spelling(end-pos:1) = '.' exit perform end-if
            add 1 to end-pos
        end-perform
        move end-pos to part-size
        subtract start-pos from part-size
        call 'name-intern' using kernel-state kind-id current-id number-val
            spelling(start-pos:part-size) part-size next-id
        move next-id to current-id
        move end-pos to start-pos
        add 1 to start-pos
    end-perform
    move current-id to result-id
    goback.
end program builtin-name.
