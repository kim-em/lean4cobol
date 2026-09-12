identification division.
program-id. parser-expression.
data division.
local-storage section.
01 root-id binary-long unsigned value 1.
01 data-id binary-long unsigned.
01 token-id binary-long unsigned.
01 array-id binary-long unsigned.
01 i binary-long unsigned.
01 field-name pic x(32).
01 category-id binary-long unsigned.
01 number-val binary-double unsigned.
01 handle-val binary-long unsigned.
01 zero-val binary-long unsigned.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 arg-c-val binary-long unsigned.
01 arg-d-val binary-long unsigned.
01 text-start binary-long unsigned.
01 text-size binary-long unsigned.
01 tmp-list binary-long unsigned.
01 ignored-id binary-long unsigned.
01 expr-tags.
   02 tag-name pic x(12) occurs 12.
linkage section.
copy 'state.cpy'.
copy 'parser-state.cpy'.
copy 'parser-map.cpy'.
copy 'json.cpy'.
01 result-id binary-long unsigned.
procedure division using kernel-state parser-state json-state result-id.
    move 0 to result-id
    if verdict not = 0 goback end-if
    set address of json-arena to json-ptr
    move 'bvar' to tag-name(1)
    move 'sort' to tag-name(2)
    move 'const' to tag-name(3)
    move 'app' to tag-name(4)
    move 'lam' to tag-name(5)
    move 'forallE' to tag-name(6)
    move 'letE' to tag-name(7)
    move 'proj' to tag-name(8)
    move 'natVal' to tag-name(9)
    move 'strVal' to tag-name(10)
    move 'fvar' to tag-name(11)
    move 'mdata' to tag-name(12)
    perform varying k from 0 by 1 until k = 12
        call 'json-field' using json-state root-id
            function trim(tag-name(k + 1)) data-id
        if data-id not = 0 exit perform end-if
    end-perform
    if k = 12 or k = 10 perform invalid-input goback end-if
    evaluate k
      when 0
        move data-id to token-id perform natural32
        move number-val to a
      when 1
        move 2 to category-id
        move data-id to token-id perform reference-id
        move handle-val to a
      when 2
        move 1 to category-id move 'name' to field-name
        perform field-reference move handle-val to a
        call 'json-field' using json-state data-id 'us' array-id
        if array-id = 0 perform invalid-input goback end-if
        if json-kind(array-id) not = 'A'
            perform invalid-input goback
        end-if
        move 2 to category-id
        compute i = json-next(array-id) - 1
        perform until i <= array-id or verdict not = 0
            move i to token-id perform reference-id
            call 'list-intern' using kernel-state handle-val b tmp-list
            move tmp-list to b
            subtract 1 from i
        end-perform
      when 3
        move 3 to category-id move 'fn' to field-name
        perform field-reference move handle-val to a
        move 'arg' to field-name
        perform field-reference move handle-val to b
      when 4 when 5 when 6
        move 1 to category-id move 'name' to field-name
        perform field-reference
        move 3 to category-id move 'type' to field-name
        perform field-reference move handle-val to a
        move 'body' to field-name
        perform field-reference
        if k = 6 move handle-val to arg-c-val else move handle-val to b end-if
        if verdict not = 0 goback end-if
        if k = 6
            move 'value' to field-name
            perform field-reference move handle-val to b
            call 'json-field' using json-state data-id 'nondep' token-id
            if token-id = 0 perform invalid-input goback end-if
            evaluate json-kind(token-id)
              when 'T' move 1 to arg-d-val
              when 'F' move 0 to arg-d-val
              when other perform invalid-input
            end-evaluate
        else
            call 'json-field' using json-state data-id 'binderInfo'
                token-id
            if token-id = 0 perform invalid-input goback end-if
            if json-kind(token-id) not = 'S'
                perform invalid-input goback
            end-if
            evaluate json-decoded(json-start(token-id):json-size(token-id))
              when 'default' when 'implicit' when 'strictImplicit'
              when 'instImplicit' continue
              when other perform invalid-input
            end-evaluate
        end-if
      when 7
        move 1 to category-id move 'typeName' to field-name
        perform field-reference move handle-val to a
        call 'json-field' using json-state data-id 'idx' token-id
        perform natural32 move number-val to b
        move 3 to category-id move 'struct' to field-name
        perform field-reference move handle-val to arg-c-val
      when 8 when 9
        if json-kind(data-id) not = 'S'
            perform invalid-input goback
        end-if
        move json-start(data-id) to text-start
        move json-size(data-id) to text-size
        if k = 8
            if text-size = 0 perform invalid-input goback end-if
            perform varying i from text-start by 1
                until i >= text-start + text-size
                if json-decoded(i:1) < '0' or > '9'
                    perform invalid-input goback
                end-if
            end-perform
            perform until text-size = 1 or json-decoded(text-start:1) not = '0'
                add 1 to text-start subtract 1 from text-size
            end-perform
        end-if
        call 'blob-intern' using kernel-state json-decoded(text-start:)
            text-size a
      when 11
        move 3 to category-id move 'expr' to field-name
        perform field-reference move handle-val to a
        call 'json-field' using json-state data-id 'data' token-id
        if token-id = 0 perform invalid-input goback end-if
        if json-kind(token-id) not = 'O' perform invalid-input end-if
    end-evaluate
    if scan-status not = 0 move scan-status to verdict end-if
    if verdict = 0
        call 'expr-intern' using kernel-state k a b arg-c-val arg-d-val result-id
    end-if
    goback.
invalid-input.
    if verdict = 0
        if scan-status = 0 move 1 to verdict
        else move scan-status to verdict end-if
    end-if.
natural32.
    if verdict not = 0 exit paragraph end-if
    call 'json-natural' using json-state token-id number-val
    if scan-status not = 0 move scan-status to verdict end-if
    if verdict = 0 and number-val > 4294967295 move 2 to verdict end-if.
field-reference.
    if verdict not = 0 exit paragraph end-if
    call 'json-field' using json-state data-id function trim(field-name)
        token-id
    perform reference-id.
reference-id.
    if verdict not = 0 exit paragraph end-if
    call 'json-natural' using json-state token-id number-val
    if scan-status not = 0 move scan-status to verdict exit paragraph end-if
    call 'id-lookup' using parser-state category-id number-val zero-val
        handle-val verdict
    if handle-val = 0 perform invalid-input end-if.
end program parser-expression.
