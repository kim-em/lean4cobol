*> GnuCOBOL ALLOCATE is capped below 2 GiB. Standard libc storage calls
*> permit larger arenas; all node processing and initialization remain COBOL.
identification division.
program-id. arena-reserve.
data division.
local-storage section.
01 new-ptr usage pointer.
01 cursor-ptr usage pointer.
01 new-cap binary-long unsigned.
01 old-bytes binary-double unsigned.
01 new-bytes binary-double unsigned.
01 remaining-bytes binary-double unsigned.
01 chunk-size binary-long unsigned.
linkage section.
01 arena-ptr usage pointer.
01 arena-cap binary-long unsigned.
01 wanted binary-long unsigned.
01 item-size binary-long unsigned.
01 status-code binary-long signed.
01 chunk-data based pic x(67108864).
procedure division using arena-ptr arena-cap wanted item-size status-code.
    if status-code not = 0 or wanted <= arena-cap goback end-if
    move arena-cap to new-cap
    if new-cap < 16 move 16 to new-cap end-if
    perform until new-cap >= wanted
        if new-cap >= 1073741824
            move 2 to status-code goback
        end-if
        multiply 2 by new-cap
    end-perform
    compute new-bytes = new-cap * item-size
    compute old-bytes = arena-cap * item-size
    call static "realloc" using by value arena-ptr new-bytes
        returning new-ptr
    if new-ptr = null move 2 to status-code goback end-if
    set cursor-ptr to new-ptr
    set cursor-ptr up by old-bytes
    move new-bytes to remaining-bytes
    subtract old-bytes from remaining-bytes
    perform until remaining-bytes = 0
        move 67108864 to chunk-size
        if remaining-bytes < chunk-size
            move remaining-bytes to chunk-size
        end-if
        set address of chunk-data to cursor-ptr
        move all low-values to chunk-data(1:chunk-size)
        set cursor-ptr up by chunk-size
        subtract chunk-size from remaining-bytes
    end-perform
    set arena-ptr to new-ptr
    move new-cap to arena-cap
    goback.
end program arena-reserve.

identification division.
program-id. arena-release.
data division.
linkage section.
01 arena-ptr usage pointer.
procedure division using arena-ptr.
    call static "free" using by value arena-ptr returning omitted
    set arena-ptr to null
    goback.
end program arena-release.

identification division.
program-id. kernel-init.
data division.
local-storage section.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 out-id binary-long unsigned.
01 n binary-double unsigned.
01 empty-text pic x.
linkage section.
copy 'state.cpy'.
procedure division using kernel-state.
    initialize kernel-state
    move 50000 to recursion-limit fuel-rec-depth
    move 100000 to fuel-whnf
    move 1000000 to fuel-whnf-eager
    move 1000 to fuel-lazy-delta fuel-eta-expand fuel-inductive
    call 'name-intern' using kernel-state k a n empty-text b out-id
    call 'level-intern' using kernel-state k a b out-id
    goback.
end program kernel-init.

identification division.
program-id. kernel-free.
data division.
linkage section.
copy 'state.cpy'.
procedure division using kernel-state.
    call 'tc-cache-free' using kernel-state
    if name-ptr not = null call 'arena-release' using name-ptr end-if
    if name-hptr not = null call 'arena-release' using name-hptr end-if
    if byte-ptr not = null call 'arena-release' using byte-ptr end-if
    if level-ptr not = null call 'arena-release' using level-ptr end-if
    if level-hptr not = null call 'arena-release' using level-hptr end-if
    if decl-ptr not = null call 'arena-release' using decl-ptr end-if
    if rule-ptr not = null call 'arena-release' using rule-ptr end-if
    if local-ptr not = null call 'arena-release' using local-ptr end-if
    if expr-ptr not = null call 'arena-release' using expr-ptr end-if
    if expr-hptr not = null call 'arena-release' using expr-hptr end-if
    if list-ptr not = null call 'arena-release' using list-ptr end-if
    if list-hptr not = null call 'arena-release' using list-hptr end-if
    if blob-ptr not = null call 'arena-release' using blob-ptr end-if
    if blob-hptr not = null call 'arena-release' using blob-hptr end-if
    goback.
end program kernel-free.
