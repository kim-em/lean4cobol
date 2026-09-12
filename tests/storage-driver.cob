*> Exercise live-cell preservation across growth and transient-cell reuse.
identification division.
program-id. storage-test.
data division.
working-storage section.
copy 'state.cpy'.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 arg-c-val binary-long unsigned.
01 arg-d-val binary-long unsigned.
01 result-id binary-long unsigned.
01 list-id binary-long unsigned.
01 saved-exprs binary-long unsigned.
01 saved-lists binary-long unsigned.
01 i binary-long unsigned.
01 pass-id binary-long unsigned.
01 argument-text pic x(16).
01 buffer-ptr usage pointer.
01 buffer-cap binary-long unsigned.
01 wanted binary-long unsigned value 32.
01 width binary-long unsigned value 40.
01 wide-zero binary-double unsigned.
01 name-u binary-long unsigned.
01 name-v binary-long unsigned.
01 level-u binary-long unsigned.
01 sort-u binary-long unsigned.
01 params-u binary-long unsigned.
01 params-v binary-long unsigned.
01 zero-depth binary-long unsigned.
linkage section.
copy 'expr.cpy'.
01 buffer-data based.
   02 buffer-row occurs 1 to unbounded depending on buffer-cap.
      03 buffer-cell pic x(40).
procedure division.
    call 'kernel-init' using kernel-state
    perform varying i from 1 by 1 until i > 1000
        move i to a
        call 'expr-intern' using kernel-state k a b arg-c-val arg-d-val result-id
        call 'list-intern' using kernel-state result-id list-id a
        move a to list-id
    end-perform
    move expr-count to saved-exprs
    move list-count to saved-lists
    perform varying pass-id from 1 by 1 until pass-id > 2
        move 10 to k
        perform varying i from 1 by 1 until i > 2000
            move i to a
            call 'expr-intern' using kernel-state k a b arg-c-val arg-d-val result-id
            call 'list-intern' using kernel-state result-id list-id a
            move a to list-id
        end-perform
        call 'expr-rewind' using kernel-state saved-exprs
        call 'list-rewind' using kernel-state saved-lists
        move saved-lists to list-id
        move 0 to k
        perform varying i from 1 by 1 until i > 1000
            move i to a
            call 'expr-intern' using kernel-state k a b arg-c-val arg-d-val result-id
            if result-id not = i move 3 to verdict end-if
        end-perform
    end-perform
    perform varying i from 1 by 1 until i > 1000
        compute b = i - 1
        call 'list-intern' using kernel-state i b a
        if a not = i move 3 to verdict end-if
    end-perform
    move 0 to b
    move 3000 to a
    call 'expr-intern' using kernel-state k a b arg-c-val arg-d-val result-id
    set address of expr-arena to expr-ptr
    if expr-has-fvar(result-id) not = 0 or expr-lbvr(result-id) not = 3001
        move 3 to verdict
    end-if
    call 'arena-reserve' using buffer-ptr buffer-cap wanted width verdict
    set address of buffer-data to buffer-ptr
    move 'preserved' to buffer-cell(1)
    accept argument-text from argument-value
        on exception move spaces to argument-text
    end-accept
    if argument-text = '--large' move 67108864 to wanted
    else move 128 to wanted end-if
    call 'arena-reserve' using buffer-ptr buffer-cap wanted width verdict
    if verdict not = 0 stop run returning verdict end-if
    set address of buffer-data to buffer-ptr
    if buffer-cell(1)(1:9) not = 'preserved' or
        buffer-cell(buffer-cap) not = low-values
        move 3 to verdict
    end-if
    move 'last' to buffer-cell(buffer-cap)
    if buffer-cell(buffer-cap)(1:4) not = 'last' move 3 to verdict end-if
    call 'arena-release' using buffer-ptr
    *> Validation caches must distinguish parameter lists in one context.
    move 1 to k a width
    call 'name-intern' using kernel-state k a wide-zero 'u' width name-u
    call 'name-intern' using kernel-state k a wide-zero 'v' width name-v
    move 4 to k move 0 to b
    call 'level-intern' using kernel-state k name-u b level-u
    move 1 to k
    call 'expr-intern' using kernel-state k level-u b b b sort-u
    call 'list-intern' using kernel-state name-u b params-u
    call 'list-intern' using kernel-state name-v b params-v
    call 'expr-params-valid' using kernel-state sort-u params-u zero-depth
    if verdict not = 0 stop run returning 3 end-if
    call 'expr-params-valid' using kernel-state sort-u params-v zero-depth
    if verdict not = 1 stop run returning 3 end-if
    move 0 to verdict
    call 'kernel-free' using kernel-state
    display 'arena growth, hash reclamation, and metadata reuse checked'
    stop run returning verdict.
end program storage-test.
