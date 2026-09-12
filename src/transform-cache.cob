identification division.
program-id. transform-cache.
data division.
local-storage section.
copy 'hash-native.cpy'.
01 half-cap usage index.
01 hash-val binary-double unsigned.
01 slot-id usage index.
01 slot-quot usage index.
01 i binary-long unsigned.
01 old-ptr usage pointer.
01 old-cap binary-long unsigned.
01 wanted binary-long unsigned.
01 width binary-long unsigned value 12.
linkage section.
copy 'state.cpy'.
copy 'transform.cpy'.
copy 'transform-views.cpy'.
01 key-expr binary-long unsigned.
01 key-depth binary-long unsigned.
01 put-val binary-long unsigned.
01 result-id binary-long unsigned.
01 old-map based.
   02 old-entry occurs 1 to 67108864 depending on old-cap.
      03 old-expr binary-long unsigned.
      03 old-depth binary-long unsigned.
      03 old-result binary-long unsigned.
procedure division using kernel-state transform-state key-expr key-depth
    put-val result-id.
    move 0 to result-id
    if verdict not = 0 goback end-if
    move tx-cache-cap to half-cap
    divide 2 into half-cap
    if put-val not = 0 and tx-cache-count >= half-cap
        set old-ptr to tx-cache-ptr
        move tx-cache-cap to old-cap
        compute wanted = function max(32, tx-cache-cap * 2)
        move 0 to tx-cache-cap
        set tx-cache-ptr to null
        call 'arena-reserve' using tx-cache-ptr tx-cache-cap wanted width verdict
        if verdict not = 0
            set tx-cache-ptr to old-ptr move old-cap to tx-cache-cap
            goback
        end-if
        set address of tx-cache to tx-cache-ptr
        set address of old-map to old-ptr
        perform varying i from 1 by 1 until i > old-cap
            if old-result(i) not = 0
                move 0 to hash-acc
                move old-expr(i) to hash-input perform hash-mix
                move old-depth(i) to hash-input perform hash-mix
                move hash-acc to hash-val
                move hash-val to slot-id
                move slot-id to slot-quot
                divide tx-cache-cap into slot-quot
                multiply tx-cache-cap by slot-quot
                subtract slot-quot from slot-id
                add 1 to slot-id
                perform until tx-result(slot-id) = 0
                    add 1 to slot-id
                    if slot-id > tx-cache-cap move 1 to slot-id end-if
                end-perform
                move old-entry(i) to tx-slot(slot-id)
            end-if
        end-perform
        if old-ptr not = null call 'arena-release' using old-ptr end-if
    end-if
    if tx-cache-cap = 0 goback end-if
    set address of tx-cache to tx-cache-ptr
    move 0 to hash-acc
    move key-expr to hash-input perform hash-mix
    move key-depth to hash-input perform hash-mix
    move hash-acc to hash-val
    move hash-val to slot-id
    move slot-id to slot-quot
    divide tx-cache-cap into slot-quot
    multiply tx-cache-cap by slot-quot
    subtract slot-quot from slot-id
    add 1 to slot-id
    perform until tx-result(slot-id) = 0
        if tx-expr(slot-id) = key-expr and tx-depth(slot-id) = key-depth
            if put-val not = 0 move put-val to tx-result(slot-id) end-if
            move tx-result(slot-id) to result-id goback
        end-if
        add 1 to slot-id
        if slot-id > tx-cache-cap move 1 to slot-id end-if
    end-perform
    if put-val not = 0
        add 1 to tx-cache-count
        move key-expr to tx-expr(slot-id)
        move key-depth to tx-depth(slot-id)
        move put-val to tx-result(slot-id) result-id
    end-if
    goback.
copy 'hash-mix.cpy'.
end program transform-cache.
