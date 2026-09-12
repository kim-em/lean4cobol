identification division.
program-id. parser-declaration.
data division.
local-storage section.
01 root-id binary-long unsigned value 1.
01 data-id binary-long unsigned.
01 package-id binary-long unsigned.
01 array-id binary-long unsigned.
01 array-end binary-long unsigned.
01 i binary-long unsigned.
01 k binary-long unsigned.
01 field-name pic x(16).
linkage section.
copy 'state.cpy'.
copy 'parser-state.cpy'.
copy 'parser-map.cpy'.
copy 'json.cpy'.
procedure division using kernel-state parser-state json-state.
    if verdict not = 0 goback end-if
    set address of json-arena to json-ptr
    perform varying k from 0 by 1 until k > 7
        evaluate k
          when 0 move 'axiom' to field-name
          when 1 move 'def' to field-name
          when 2 move 'thm' to field-name
          when 3 move 'opaque' to field-name
          when 4 move 'inductive' to field-name
          when 5 when 6 continue
          when 7 move 'quot' to field-name
        end-evaluate
        if k not = 5 and k not = 6
            call 'json-field' using json-state root-id function trim(field-name) data-id
            if data-id not = 0 exit perform end-if
        end-if
    end-perform
    if data-id = 0 move 1 to pending-declarations goback end-if
    if k not = 4
        call 'parser-constant' using kernel-state parser-state json-state data-id k
        goback
    end-if
    if json-kind(data-id) not = 'O' move 1 to verdict goback end-if
    move data-id to package-id
    perform varying k from 4 by 1 until k > 6 or verdict not = 0
        evaluate k
          when 4 move 'types' to field-name
          when 5 move 'ctors' to field-name
          when 6 move 'recs' to field-name
        end-evaluate
        call 'json-field' using json-state package-id function trim(field-name) array-id
        if array-id = 0 move 1 to verdict exit perform end-if
        if json-kind(array-id) not = 'A' move 1 to verdict exit perform end-if
        move json-next(array-id) to array-end
        move array-id to i
        add 1 to i
        perform until i >= array-end or verdict not = 0
            move i to data-id
            call 'parser-constant' using kernel-state parser-state json-state data-id k
            move json-next(i) to i
        end-perform
    end-perform
    goback.
end program parser-declaration.

identification division.
program-id. parser-constant.
data division.
local-storage section.
01 root-id binary-long unsigned value 1.
01 token-id binary-long unsigned.
01 array-id binary-long unsigned.
01 i binary-long unsigned.
01 n binary-long unsigned.
01 ty binary-long unsigned.
01 val binary-long unsigned.
01 params binary-long unsigned.
01 all-names binary-long unsigned.
01 hints-id binary-long unsigned.
01 hints-kind binary-long unsigned.
01 hints-height binary-long unsigned.
01 unsafe-val binary-char unsigned.
01 category-id binary-long unsigned.
01 number-val binary-double unsigned.
01 zero-val binary-long unsigned.
01 handle-val binary-long unsigned.
01 field-name pic x(32).
01 tmp-list binary-long unsigned.
01 wanted binary-long unsigned.
01 width binary-long unsigned.
01 declaration-id binary-long unsigned.
01 saved-data binary-long unsigned.
01 rule-id binary-long unsigned.
01 rule-list binary-long unsigned.
01 list-out binary-long unsigned.
01 array-end binary-long unsigned.
01 bool-val binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'parser-state.cpy'.
copy 'parser-map.cpy'.
copy 'json.cpy'.
copy 'names.cpy'.
copy 'declarations.cpy'.
01 data-id binary-long unsigned.
01 k binary-long unsigned.
procedure division using kernel-state parser-state json-state data-id k.
    if verdict not = 0 goback end-if
    set address of json-arena to json-ptr
    if json-kind(data-id) not = 'O' move 1 to verdict goback end-if
    move 1 to category-id move 'name' to field-name
    perform field-reference move handle-val to n
    move 3 to category-id move 'type' to field-name
    perform field-reference move handle-val to ty
    if k >= 1 and k <= 3
        move 'value' to field-name
        perform field-reference move handle-val to val
    end-if
    if verdict not = 0 goback end-if
    call 'json-field' using json-state data-id 'levelParams' array-id
    if array-id = 0 move 1 to verdict goback end-if
    if json-kind(array-id) not = 'A' move 1 to verdict goback end-if
    move 1 to category-id
    compute i = json-next(array-id) - 1
    perform until i <= array-id or verdict not = 0
        move i to token-id perform reference-id
        call 'list-intern' using kernel-state handle-val params tmp-list
        move tmp-list to params
        subtract 1 from i
    end-perform
    if verdict not = 0 goback end-if
    if (k >= 1 and k <= 4) or k = 6
        call 'json-field' using json-state data-id 'all' array-id
        if array-id = 0 move 1 to verdict goback end-if
        if json-kind(array-id) not = 'A' move 1 to verdict goback end-if
        compute i = json-next(array-id) - 1
        perform until i <= array-id or verdict not = 0
            move i to token-id perform reference-id
            call 'list-intern' using kernel-state handle-val all-names tmp-list
            move tmp-list to all-names
            subtract 1 from i
        end-perform
    end-if
    if verdict not = 0 goback end-if
    if k = 1
        call 'json-field' using json-state data-id 'hints' hints-id
        if hints-id = 0 move 1 to verdict goback end-if
        evaluate json-kind(hints-id)
          when 'S'
            evaluate json-decoded(json-start(hints-id):json-size(hints-id))
              when 'opaque' move 0 to hints-kind
              when 'abbrev' move 1 to hints-kind
              when other move 1 to verdict goback
            end-evaluate
          when 'O'
            move 2 to hints-kind
            call 'json-field' using json-state hints-id 'regular' token-id
            call 'json-natural' using json-state token-id number-val
            if scan-status not = 0 move scan-status to verdict goback end-if
            if number-val > 4294967295 move 2 to verdict goback end-if
            move number-val to hints-height
          when other move 1 to verdict goback
        end-evaluate
        call 'json-field' using json-state data-id 'safety' token-id
        if token-id = 0 move 1 to verdict goback end-if
        if json-kind(token-id) not = 'S' move 1 to verdict goback end-if
        evaluate json-decoded(json-start(token-id):json-size(token-id))
          when 'safe' continue
          when 'unsafe' when 'partial' move 1 to unsafe-val
          when other move 1 to verdict goback
        end-evaluate
    else
        if k not = 2 and k not = 7
            call 'json-field' using json-state data-id 'isUnsafe' token-id
            if token-id = 0
                if k not = 3 move 1 to verdict goback end-if
            else
                evaluate json-kind(token-id)
                  when 'T' move 1 to unsafe-val
                  when 'F' continue
                  when other move 1 to verdict goback
                end-evaluate
            end-if
        end-if
    end-if
    if scan-status not = 0 move scan-status to verdict goback end-if
    set address of name-arena to name-ptr
    if name-decl(n) not = 0 move 1 to verdict goback end-if
    move decl-count to wanted
    add 1 to wanted
    move length of decl-node to width
    call 'arena-reserve' using decl-ptr decl-cap wanted width verdict
    if verdict not = 0 goback end-if
    set address of decl-arena to decl-ptr
    add 1 to decl-count
    move decl-count to name-decl(n)
    move n to decl-name(decl-count)
    move k to decl-kind(decl-count)
    move params to decl-params(decl-count)
    move all-names to decl-all(decl-count)
    move hints-kind to decl-hints(decl-count)
    move hints-height to decl-height(decl-count)
    move ty to decl-type(decl-count)
    move val to decl-value(decl-count)
    move unsafe-val to decl-unsafe(decl-count)
    move decl-count to declaration-id
    evaluate k
      when 4
        move 'ctors' to field-name perform name-list
        move list-out to decl-ctors(declaration-id)
        move 'numNested' to field-name perform natural-field
        move handle-val to decl-num-nested(declaration-id)
        move 'isRec' to field-name perform bool-field
        move bool-val to decl-is-rec(declaration-id)
        move 'isReflexive' to field-name perform bool-field
        move bool-val to decl-reflexive(declaration-id)
      when 5
        move 1 to category-id move 'induct' to field-name perform field-reference
        move handle-val to decl-induct(declaration-id)
        move 'cidx' to field-name perform natural-field
        move handle-val to decl-cidx(declaration-id)
        move 'numFields' to field-name perform natural-field
        move handle-val to decl-num-fields(declaration-id)
      when 6
        move 'numMotives' to field-name perform natural-field
        move handle-val to decl-num-motives(declaration-id)
        move 'numMinors' to field-name perform natural-field
        move handle-val to decl-num-minors(declaration-id)
        move 'k' to field-name perform bool-field
        move bool-val to decl-k(declaration-id)
        perform parse-rules
        move rule-list to decl-rules(declaration-id)
      when 7
        call 'json-field' using json-state data-id 'kind' token-id
        if token-id = 0 move 1 to verdict goback end-if
        if json-kind(token-id) not = 'S' move 1 to verdict goback end-if
        evaluate json-decoded(json-start(token-id):json-size(token-id))
          when 'type' move 0 to decl-quot-kind(declaration-id)
          when 'ctor' move 1 to decl-quot-kind(declaration-id)
          when 'lift' move 2 to decl-quot-kind(declaration-id)
          when 'ind' move 3 to decl-quot-kind(declaration-id)
          when other move 1 to verdict
        end-evaluate
    end-evaluate
    if k >= 4 and k <= 6
        move 'numParams' to field-name perform natural-field
        move handle-val to decl-num-params(declaration-id)
        if k not = 5
            move 'numIndices' to field-name perform natural-field
            move handle-val to decl-num-indices(declaration-id)
        end-if
    end-if
    goback.
natural-field.
    if verdict not = 0 exit paragraph end-if
    call 'json-field' using json-state data-id function trim(field-name) token-id
    call 'json-natural' using json-state token-id number-val
    if scan-status not = 0 move scan-status to verdict exit paragraph end-if
    if number-val > 4294967295 move 2 to verdict exit paragraph end-if
    move number-val to handle-val.
bool-field.
    if verdict not = 0 exit paragraph end-if
    call 'json-field' using json-state data-id function trim(field-name) token-id
    if token-id = 0 move 1 to verdict exit paragraph end-if
    evaluate json-kind(token-id)
      when 'T' move 1 to bool-val
      when 'F' move 0 to bool-val
      when other move 1 to verdict
    end-evaluate.
name-list.
    move 0 to list-out
    if verdict not = 0 exit paragraph end-if
    call 'json-field' using json-state data-id function trim(field-name) array-id
    if array-id = 0 move 1 to verdict exit paragraph end-if
    if json-kind(array-id) not = 'A' move 1 to verdict exit paragraph end-if
    move 1 to category-id
    compute i = json-next(array-id) - 1
    perform until i <= array-id or verdict not = 0
        move i to token-id perform reference-id
        call 'list-intern' using kernel-state handle-val list-out tmp-list
        move tmp-list to list-out subtract 1 from i
    end-perform.
parse-rules.
    if verdict not = 0 exit paragraph end-if
    call 'json-field' using json-state data-id 'rules' array-id
    if array-id = 0 move 1 to verdict exit paragraph end-if
    if json-kind(array-id) not = 'A' move 1 to verdict exit paragraph end-if
    move data-id to saved-data
    move json-next(array-id) to array-end
    move array-id to i
    add 1 to i
    perform until i >= array-end or verdict not = 0
        move i to data-id
        if json-kind(data-id) not = 'O' move 1 to verdict exit perform end-if
        move rule-count to wanted
        add 1 to wanted
        move length of rule-node to width
        call 'arena-reserve' using rule-ptr rule-cap wanted width verdict
        if verdict not = 0 exit perform end-if
        set address of rule-arena to rule-ptr
        add 1 to rule-count move rule-count to rule-id
        move 1 to category-id move 'ctor' to field-name perform field-reference
        move handle-val to rule-ctor(rule-id)
        move 3 to category-id move 'rhs' to field-name perform field-reference
        move handle-val to rule-rhs(rule-id)
        move 'nfields' to field-name perform natural-field
        move handle-val to rule-fields(rule-id)
        call 'list-intern' using kernel-state rule-id rule-list tmp-list
        move tmp-list to rule-list
        move json-next(i) to i
    end-perform
    move saved-data to data-id
    call 'list-reverse' using kernel-state rule-list tmp-list
    move tmp-list to rule-list.
field-reference.
    if verdict not = 0 exit paragraph end-if
    call 'json-field' using json-state data-id function trim(field-name) token-id
    perform reference-id.
reference-id.
    if verdict not = 0 exit paragraph end-if
    call 'json-natural' using json-state token-id number-val
    if scan-status not = 0 move scan-status to verdict exit paragraph end-if
    call 'id-lookup' using parser-state category-id number-val zero-val handle-val verdict
    if handle-val = 0 move 1 to verdict end-if.
end program parser-constant.
