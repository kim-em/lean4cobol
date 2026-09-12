*> Sparse external IDs are distinct from interned, 1-based arena handles.
identification division.
program-id. id-lookup.
data division.
local-storage section.
01 hash-val binary-double unsigned.
01 dense-size binary-long unsigned.
01 dense-index binary-long unsigned.
01 dense-width binary-long unsigned value 4.
01 slot-id binary-long unsigned.
01 i binary-long unsigned.
01 old-ptr usage pointer.
01 old-cap binary-long unsigned.
01 wanted binary-long unsigned.
01 width binary-long unsigned value 16.
linkage section.
copy 'parser-state.cpy'.
copy 'parser-map.cpy'.
01 category-id binary-long unsigned.
01 external-id binary-double unsigned.
*> put-val = 0 is lookup; otherwise insert/replace and return the value.
01 put-val binary-long unsigned.
01 result-id binary-long unsigned.
01 status-code binary-long signed.
01 dense-data based.
   02 dense-value binary-long unsigned occurs 1 to unbounded
       depending on dense-size.
01 old-map based.
   02 old-entry occurs 1 to unbounded depending on old-cap.
      03 old-category binary-long unsigned.
      03 old-key binary-double unsigned.
      03 old-value binary-long unsigned.
procedure division using parser-state category-id external-id
    put-val result-id status-code.
    move 0 to result-id
    if status-code not = 0 goback end-if
    *> Standard exports use consecutive IDs. A compact direct table handles
    *> that prefix; arbitrary/sparse 64-bit IDs retain the original hash map.
    *> A zero direct slot always falls through, including old sparse entries
    *> that a later direct-table expansion has covered.
    if category-id < 1 or category-id > 3
        move 3 to status-code goback
    end-if
    if put-val not = 0 and external-id = dense-cap(category-id)
        move external-id to wanted
        add 1 to wanted
        call 'arena-reserve' using dense-ptr(category-id)
            dense-cap(category-id) wanted dense-width status-code
        if status-code not = 0 goback end-if
    end-if
    if external-id < dense-cap(category-id)
        move dense-cap(category-id) to dense-size
        set address of dense-data to dense-ptr(category-id)
        move external-id to dense-index
        add 1 to dense-index
        if put-val not = 0
            move put-val to dense-value(dense-index)
        end-if
        move dense-value(dense-index) to result-id
        if result-id not = 0 goback end-if
    end-if
    if put-val not = 0 and map-count * 2 >= map-cap
        set old-ptr to map-ptr
        move map-cap to old-cap
        compute wanted = function max(32, map-cap * 2)
        move 0 to map-cap
        set map-ptr to null
        call 'arena-reserve' using map-ptr map-cap wanted width
            status-code
        if status-code not = 0
            set map-ptr to old-ptr move old-cap to map-cap
            goback
        end-if
        set address of id-map to map-ptr
        set address of old-map to old-ptr
        perform varying i from 1 by 1 until i > old-cap
            if old-value(i) not = 0
                compute hash-val = function mod(old-key(i),
                    4294967291) * 65599 + old-category(i)
                compute slot-id = function mod(hash-val, map-cap) + 1
                perform until id-value(slot-id) = 0
                    add 1 to slot-id
                    if slot-id > map-cap move 1 to slot-id end-if
                end-perform
                move old-entry(i) to id-entry(slot-id)
            end-if
        end-perform
        if old-ptr not = null call 'arena-release' using old-ptr end-if
    end-if
    if map-cap = 0 goback end-if
    set address of id-map to map-ptr
    compute hash-val = function mod(external-id, 4294967291) *
        65599 + category-id
    compute slot-id = function mod(hash-val, map-cap) + 1
    perform until id-value(slot-id) = 0
        if id-category(slot-id) = category-id and
            id-key(slot-id) = external-id
            if put-val not = 0 move put-val to id-value(slot-id)
            end-if
            move id-value(slot-id) to result-id goback
        end-if
        add 1 to slot-id
        if slot-id > map-cap move 1 to slot-id end-if
    end-perform
    if put-val not = 0
        add 1 to map-count
        move category-id to id-category(slot-id)
        move external-id to id-key(slot-id)
        move put-val to id-value(slot-id) result-id
    end-if
    goback.
end program id-lookup.
