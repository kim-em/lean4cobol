*> Independent cache families share an open-addressed table. Values are nonzero
*> expression handles (or 1 for a failed-pair marker); lookup never inserts.
identification division.
program-id. tc-cache.
data division.
local-storage section.
01 half-cap usage index.
copy 'hash-native.cpy'.
01 old-ptr usage pointer.
01 old-cap binary-long unsigned.
01 wanted binary-long unsigned.
01 width binary-long unsigned value 16.
01 slot-id usage index.
01 slot-quot usage index.
01 i binary-long unsigned.
01 h binary-double unsigned.
linkage section.
copy 'state.cpy'.
01 family binary-long unsigned.
01 key-a binary-long unsigned.
01 key-b binary-long unsigned.
01 value-id binary-long unsigned.
01 result-id binary-long unsigned.
01 cache-data based.
   02 cache-entry occurs 1 to 67108864 depending on tc-cache-cap.
      03 cache-family binary-long unsigned.
      03 cache-a binary-long unsigned.
      03 cache-b binary-long unsigned.
      03 cache-value binary-long unsigned.
01 old-data based.
   02 old-entry occurs 1 to 67108864 depending on old-cap.
      03 old-family binary-long unsigned.
      03 old-a binary-long unsigned.
      03 old-b binary-long unsigned.
      03 old-value binary-long unsigned.
procedure division using kernel-state family key-a key-b value-id result-id.
    move 0 to result-id
    if verdict not = 0 goback end-if
    if value-id = 0 and tc-cache-count = 0 goback end-if
    move tc-cache-cap to half-cap
    divide 2 into half-cap
    if value-id not = 0 and tc-cache-count >= half-cap
        set old-ptr to tc-cache-ptr
        move tc-cache-cap to old-cap
        compute wanted = function max(32, old-cap * 2)
        set tc-cache-ptr to null move 0 to tc-cache-cap
        call 'arena-reserve' using tc-cache-ptr tc-cache-cap wanted width verdict
        if verdict not = 0
            set tc-cache-ptr to old-ptr move old-cap to tc-cache-cap goback
        end-if
        set address of cache-data to tc-cache-ptr
        if old-ptr not = null
            set address of old-data to old-ptr
            perform varying i from 1 by 1 until i > old-cap
                if old-value(i) not = 0
                    move old-family(i) to hash-acc
                    move old-a(i) to hash-input perform hash-mix
                    move old-b(i) to hash-input perform hash-mix
                    move hash-acc to h
                    move h to slot-id
                    move slot-id to slot-quot
                    divide tc-cache-cap into slot-quot
                    multiply tc-cache-cap by slot-quot
                    subtract slot-quot from slot-id
                    add 1 to slot-id
                    perform until cache-value(slot-id) = 0
                        add 1 to slot-id
                        if slot-id > tc-cache-cap move 1 to slot-id end-if
                    end-perform
                    move old-entry(i) to cache-entry(slot-id)
                end-if
            end-perform
            call 'arena-release' using old-ptr
        end-if
    end-if
    set address of cache-data to tc-cache-ptr
    move family to hash-acc
    move key-a to hash-input perform hash-mix
    move key-b to hash-input perform hash-mix
    move hash-acc to h
    move h to slot-id
    move slot-id to slot-quot
    divide tc-cache-cap into slot-quot
    multiply tc-cache-cap by slot-quot
    subtract slot-quot from slot-id
    add 1 to slot-id
    perform until cache-value(slot-id) = 0
        if cache-family(slot-id) = family and cache-a(slot-id) = key-a and cache-b(slot-id) = key-b
            move cache-value(slot-id) to result-id
            if value-id not = 0 move value-id to cache-value(slot-id) end-if
            goback
        end-if
        add 1 to slot-id
        if slot-id > tc-cache-cap move 1 to slot-id end-if
    end-perform
    if value-id not = 0
        move family to cache-family(slot-id)
        move key-a to cache-a(slot-id) move key-b to cache-b(slot-id)
        move value-id to cache-value(slot-id)
        add 1 to tc-cache-count
    end-if
    goback.
copy 'hash-mix.cpy'.
end program tc-cache.

identification division.
program-id. tc-cache-free.
data division.
linkage section.
copy 'state.cpy'.
procedure division using kernel-state.
    if tc-cache-ptr not = null call 'arena-release' using tc-cache-ptr end-if
    set tc-cache-ptr to null
    move 0 to tc-cache-count tc-cache-cap
    goback.
end program tc-cache-free.
