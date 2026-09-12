identification division.
program-id. parser-record.
data division.
local-storage section.
01 fast-handled binary-char unsigned.
01 root-id binary-long unsigned value 1.
01 token-id binary-long unsigned.
01 data-id binary-long unsigned.
01 saved-token binary-long unsigned.
01 parent-id binary-long unsigned.
01 index-id binary-double unsigned.
01 number-val binary-double unsigned.
01 name-num binary-double unsigned.
01 category-id binary-long unsigned.
01 kind-id binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 zero-val binary-long unsigned.
01 result-id binary-long unsigned.
01 ignored-id binary-long unsigned.
01 text-size binary-long unsigned.
01 text-start binary-long unsigned value 1.
01 field-count binary-long unsigned.
01 i binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'parser-state.cpy'.
copy 'parser-map.cpy'.
copy 'json.cpy'.
procedure division using kernel-state parser-state json-state.
    if verdict not = 0 goback end-if
    call 'parser-fast-expression' using kernel-state parser-state json-state fast-handled
    if fast-handled = 1 goback end-if
    call 'json-parse' using json-state
    if scan-status not = 0
        move scan-status to verdict goback
    end-if
    set address of json-arena to json-ptr
    if json-kind(1) not = 'O' move 1 to verdict goback end-if
    move 2 to i
    perform until i >= json-next(1)
        add 1 to field-count
        move json-next(i + 1) to i
    end-perform
    call 'json-field' using json-state root-id 'meta' token-id
    if token-id not = 0
        if seen-meta = 1 or record-count not = 1 or field-count not = 1
            move 1 to verdict goback
        end-if
        move token-id to parent-id
        call 'json-field' using json-state parent-id 'format' token-id
        move token-id to parent-id
        call 'json-field' using json-state parent-id 'version' token-id
        if scan-status not = 0 or token-id = 0
            move 1 to verdict goback
        end-if
        if json-kind(token-id) not = 'S'
            move 1 to verdict goback
        end-if
        if json-size(token-id) not = 5 or
            json-decoded(json-start(token-id):5) not = '3.1.0'
            move 2 to verdict goback
        end-if
        move 1 to seen-meta
        move 0 to index-id
        move 1 to a category-id
        call 'id-lookup' using parser-state category-id index-id a
            ignored-id verdict
        move 2 to category-id
        call 'id-lookup' using parser-state category-id index-id a
            ignored-id verdict
        goback
    end-if
    if seen-meta = 0 move 1 to verdict goback end-if
    call 'json-field' using json-state root-id 'in' token-id
    if token-id not = 0
        if field-count not = 2 move 1 to verdict goback end-if
        move 1 to category-id
        call 'json-natural' using json-state token-id index-id
        perform parse-name
    else
        call 'json-field' using json-state root-id 'il' token-id
        if token-id not = 0
            if field-count not = 2 move 1 to verdict goback end-if
            move 2 to category-id
            call 'json-natural' using json-state token-id index-id
            perform parse-level
        else
            call 'json-field' using json-state root-id 'ie' token-id
            if token-id not = 0
                if field-count not = 2 move 1 to verdict goback end-if
                move 3 to category-id
                call 'json-natural' using json-state token-id index-id
                if scan-status not = 0 move scan-status to verdict goback end-if
                call 'parser-expression' using kernel-state parser-state
                    json-state result-id
            else
                if field-count not = 1 move 1 to verdict goback end-if
                call 'parser-declaration' using kernel-state parser-state json-state
            end-if
        end-if
    end-if
    if scan-status not = 0 move scan-status to verdict end-if
    if verdict = 0 and category-id not = 0
        call 'id-lookup' using parser-state category-id index-id
            result-id ignored-id verdict
    end-if
    goback.
parse-name.
    call 'json-field' using json-state root-id 'str' data-id
    if data-id = 0
        move 2 to kind-id
        call 'json-field' using json-state root-id 'num' data-id
    else move 1 to kind-id end-if
    if data-id = 0 move 1 to verdict exit paragraph end-if
    call 'json-field' using json-state data-id 'pre' token-id
    call 'json-natural' using json-state token-id number-val
    call 'id-lookup' using parser-state category-id number-val
        zero-val a verdict
    if a = 0 move 1 to verdict exit paragraph end-if
    if kind-id = 1
        call 'json-field' using json-state data-id 'str' token-id
        if token-id = 0 move 1 to verdict exit paragraph end-if
        if json-kind(token-id) not = 'S'
            move 1 to verdict exit paragraph
        end-if
        move json-size(token-id) to text-size
        move json-start(token-id) to text-start
    else
        call 'json-field' using json-state data-id 'i' token-id
        call 'json-natural' using json-state token-id name-num
    end-if
    if scan-status = 0
        call 'name-intern' using kernel-state kind-id a name-num
            json-decoded(text-start:) text-size result-id
    end-if.
parse-level.
    call 'json-field' using json-state root-id 'succ' data-id
    if data-id not = 0
        move 1 to kind-id
    else
        call 'json-field' using json-state root-id 'max' data-id
        if data-id not = 0 move 2 to kind-id else
            call 'json-field' using json-state root-id 'imax' data-id
            if data-id not = 0 move 3 to kind-id else
                call 'json-field' using json-state root-id 'param'
                    data-id
                if data-id not = 0 move 4 to kind-id else
                    move 1 to verdict exit paragraph
                end-if
            end-if
        end-if
    end-if
    if kind-id = 2 or 3
        if json-kind(data-id) not = 'A' or
            json-next(data-id) not = data-id + 3
            move 1 to verdict exit paragraph
        end-if
        move data-id to token-id
        add 1 to token-id
    else move data-id to token-id end-if
    call 'json-natural' using json-state token-id number-val
    if kind-id = 4 move 1 to category-id end-if
    call 'id-lookup' using parser-state category-id number-val
        zero-val a verdict
    move 2 to category-id
    if a = 0 move 1 to verdict exit paragraph end-if
    if kind-id = 2 or 3
        move data-id to token-id
        add 2 to token-id
        call 'json-natural' using json-state token-id number-val
        call 'id-lookup' using parser-state category-id number-val
            zero-val b verdict
        if b = 0 move 1 to verdict exit paragraph end-if
    end-if
    if scan-status = 0
        call 'level-intern' using kernel-state kind-id a b result-id
    end-if.
end program parser-record.
