identification division.
program-id. blob-intern.
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
01 blob-text pic x any length.
01 text-length binary-long unsigned.
01 result-id binary-long unsigned.
copy 'blob.cpy'.
01 string-bytes based.
   02 string-byte pic x occurs 1 to 2000000000
      depending on byte-cap.
procedure division using kernel-state blob-text text-length result-id.
    move 0 to result-id
    if verdict not = 0 goback end-if
    move 0 to h
    perform varying i from 1 by 1 until i > text-length
        compute mod-input = h * 257 +
            function ord(blob-text(i:1))
    divide mod-input by 4294967291 giving mod-quotient
        remainder h
    end-perform
    if blob-count * 2 >= blob-hcap
        set old-hptr to blob-hptr
        compute wanted = function max(32, blob-hcap * 2)
        move 0 to blob-hcap
        set blob-hptr to null
        move 4 to width
        call 'arena-reserve' using blob-hptr blob-hcap wanted
            width verdict
        if verdict not = 0
            set blob-hptr to old-hptr goback
        end-if
        set address of blob-htable to blob-hptr
        set address of blob-arena to blob-ptr
        perform varying i from 1 by 1 until i > blob-count
            compute mod-input = blob-hash(i)
            divide mod-input by blob-hcap giving mod-quotient
                remainder slot-id
    add 1 to slot-id
            perform until blob-slot(slot-id) = 0
                add 1 to slot-id
                if slot-id > blob-hcap move 1 to slot-id end-if
            end-perform
            move i to blob-slot(slot-id)
        end-perform
        if old-hptr not = null call 'arena-release' using old-hptr end-if
    end-if
    set address of blob-htable to blob-hptr
    set address of blob-arena to blob-ptr
    set address of string-bytes to byte-ptr
    compute mod-input = h
    divide mod-input by blob-hcap giving mod-quotient
        remainder slot-id
    add 1 to slot-id
    perform until blob-slot(slot-id) = 0
        move blob-slot(slot-id) to node-id
        if blob-length(node-id) = text-length
            if text-length = 0
                move node-id to result-id goback
            end-if
            if string-bytes(blob-start(node-id):text-length) =
                blob-text(1:text-length)
                move node-id to result-id goback
            end-if
        end-if
        add 1 to slot-id
        if slot-id > blob-hcap move 1 to slot-id end-if
    end-perform
    move blob-count to wanted
    add 1 to wanted
    move length of blob-node to width
    call 'arena-reserve' using blob-ptr blob-cap wanted width
        verdict
    if verdict not = 0 goback end-if
    set address of blob-arena to blob-ptr
    if text-length > 0
        move byte-count to wanted
        add text-length to wanted
        move 1 to width
        call 'arena-reserve' using byte-ptr byte-cap wanted width
            verdict
        if verdict not = 0 goback end-if
        set address of string-bytes to byte-ptr
    end-if
    add 1 to blob-count
    move blob-count to result-id blob-slot(slot-id)
    move h to blob-hash(result-id)
    move text-length to blob-length(result-id)
    compute blob-start(result-id) = byte-count + 1
    if text-length > 0
        move blob-text(1:text-length) to
            string-bytes(byte-count + 1:text-length)
        add text-length to byte-count
    end-if
    goback.
end program blob-intern.
