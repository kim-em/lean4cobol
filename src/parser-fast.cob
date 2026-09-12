*> Exact canonical spellings of common expression records avoid tokenizing
*> their fixed punctuation. Everything else goes through the general parser.
*> No state is changed until the entire record matches, including EOF.
identification division.
program-id. parser-fast-expression.
data division.
local-storage section.
01 pos-id usage index.
01 digit-val usage index.
01 number-val usage index.
01 number-start usage index.
01 scan-char pic x.
01 decimal-char redefines scan-char pic 9.
01 matched binary-char unsigned value 1.
01 external-id binary-double unsigned.
01 first-id binary-double unsigned.
01 second-id binary-double unsigned.
01 category-id binary-long unsigned.
01 kind-id binary-long unsigned.
01 arg-a binary-long unsigned.
01 arg-b binary-long unsigned.
01 zero-val binary-long unsigned.
01 result-id binary-long unsigned.
01 ignored-id binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'parser-state.cpy'.
copy 'json.cpy'.
01 handled binary-char unsigned.
procedure division using kernel-state parser-state json-state handled.
    move 0 to handled
    if seen-meta = 0 or json-length < 18 or json-length > 128 goback end-if
    if json-input(1:6) not = '{"ie":' goback end-if
    move 7 to pos-id
    perform natural-number
    if matched = 0 goback end-if
    move number-val to external-id
    evaluate true
      when json-input(pos-id:13) = ',"app":{"fn":'
        move 3 to kind-id
        add 13 to pos-id
        perform natural-number
        if matched = 0 goback end-if
        move number-val to first-id
        if json-input(pos-id:7) not = ',"arg":' goback end-if
        add 7 to pos-id
        perform natural-number
        if matched = 0 goback end-if
        move number-val to second-id
        if pos-id + 1 not = json-length or json-input(pos-id:2) not = '}}'
            goback
        end-if
      when json-input(pos-id:8) = ',"bvar":'
        move 0 to kind-id
        add 8 to pos-id
        perform natural-number
        if matched = 0 goback end-if
        move number-val to arg-a
        if pos-id not = json-length or json-input(pos-id:1) not = '}' goback end-if
      when json-input(pos-id:8) = ',"sort":'
        move 1 to kind-id
        add 8 to pos-id
        perform natural-number
        if matched = 0 goback end-if
        move number-val to first-id
        if pos-id not = json-length or json-input(pos-id:1) not = '}' goback end-if
      when other goback
    end-evaluate
    move 1 to handled
    evaluate kind-id
      when 3
        move 3 to category-id
        call 'id-lookup' using parser-state category-id first-id zero-val arg-a verdict
        call 'id-lookup' using parser-state category-id second-id zero-val arg-b verdict
        if arg-a = 0 or arg-b = 0 move 1 to verdict goback end-if
      when 1
        move 2 to category-id
        call 'id-lookup' using parser-state category-id first-id zero-val arg-a verdict
        if arg-a = 0 move 1 to verdict goback end-if
    end-evaluate
    call 'expr-intern' using kernel-state kind-id arg-a arg-b zero-val zero-val result-id
    move 3 to category-id
    call 'id-lookup' using parser-state category-id external-id result-id ignored-id verdict
    goback.
natural-number.
    move 0 to number-val
    move pos-id to number-start
    perform until pos-id > json-length
        move json-input(pos-id:1) to scan-char
        if scan-char < '0' or scan-char > '9' exit perform end-if
        if pos-id > number-start and number-val = 0
            move 0 to matched exit paragraph
        end-if
        move decimal-char to digit-val
        if number-val > 214748364 or
            (number-val = 214748364 and digit-val > 7)
            move 0 to matched exit paragraph
        end-if
        multiply 10 by number-val
        add digit-val to number-val
        add 1 to pos-id
    end-perform
    if pos-id = number-start move 0 to matched end-if.
end program parser-fast-expression.
