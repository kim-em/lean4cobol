*> Small storage/substitution operations for ElimNestedInductive.
identification division.
program-id. declaration-clone.
data division.
local-storage section.
01 wanted binary-long unsigned.
01 width binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'declarations.cpy'.
01 source-id binary-long unsigned.
01 result-id binary-long unsigned.
procedure division using kernel-state source-id result-id.
    move 0 to result-id
    if verdict not = 0 goback end-if
    compute wanted = decl-count + 1 move length of decl-node to width
    call 'arena-reserve' using decl-ptr decl-cap wanted width verdict
    if verdict not = 0 goback end-if
    add 1 to decl-count move decl-count to result-id
    set address of decl-arena to decl-ptr
    if source-id not = 0 move decl-node(source-id) to decl-node(result-id) end-if
    goback.
end program declaration-clone.

identification division.
program-id. nested-bind-source.
data division.
local-storage section.
01 n binary-long unsigned.
01 old-id binary-long unsigned.
01 tmp binary-long unsigned.
01 pair-id binary-long unsigned.
01 zero-val binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
01 declaration-id binary-long unsigned.
procedure division using kernel-state ind-state declaration-id.
    if verdict not = 0 goback end-if
    set address of decl-arena to decl-ptr move decl-name(declaration-id) to n
    set address of name-arena to name-ptr move name-decl(n) to old-id
    call 'list-intern' using kernel-state old-id zero-val tmp
    call 'list-intern' using kernel-state n tmp pair-id
    call 'list-intern' using kernel-state pair-id ind-saved-bindings tmp
    move tmp to ind-saved-bindings
    set address of name-arena to name-ptr move declaration-id to name-decl(n)
    goback.
end program nested-bind-source.

identification division.
program-id. nested-restore-bindings.
data division.
local-storage section.
01 p binary-long unsigned.
01 pair-id binary-long unsigned.
01 n binary-long unsigned.
01 old-id binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'names.cpy'.
copy 'list.cpy'.
procedure division using kernel-state ind-state.
    *> Cleanup also runs after a failed check.
    move ind-saved-bindings to p
    set address of list-arena to list-ptr set address of name-arena to name-ptr
    perform until p = 0
        move list-a(p) to pair-id move list-b(p) to p
        move list-a(pair-id) to n move list-b(pair-id) to pair-id
        move list-a(pair-id) to old-id move old-id to name-decl(n)
    end-perform
    move 0 to ind-saved-bindings
    goback.
end program nested-restore-bindings.

identification division.
program-id. nested-open-params.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 dom binary-long unsigned.
01 body-id binary-long unsigned.
01 fv binary-long unsigned.
01 tmp binary-long unsigned.
01 params binary-long unsigned.
01 i binary-long unsigned.
01 zero-val binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 input-expr binary-long unsigned.
01 count-val binary-long unsigned.
01 result-params binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr count-val result-params result-expr.
    move input-expr to current-id result-expr move 0 to result-params
    perform varying i from 1 by 1 until i > count-val or verdict not = 0
        set address of expr-arena to expr-ptr
        if expr-kind(current-id) not = 4 and expr-kind(current-id) not = 5
            move 1 to verdict goback
        end-if
        move expr-a(current-id) to dom move expr-b(current-id) to body-id
        call 'local-fresh' using kernel-state dom zero-val fv
        call 'list-intern' using kernel-state fv params tmp move tmp to params
        call 'expr-instantiate1' using kernel-state body-id fv current-id
    end-perform
    call 'list-reverse' using kernel-state params result-params
    move current-id to result-expr
    goback.
end program nested-open-params.

identification division.
program-id. nested-apply-params.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 p binary-long unsigned.
01 fv binary-long unsigned.
01 body-id binary-long unsigned.
01 i binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
copy 'list.cpy'.
01 input-expr binary-long unsigned.
01 count-val binary-long unsigned.
01 params binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr count-val params result-expr.
    move input-expr to current-id result-expr move params to p
    perform varying i from 1 by 1 until i > count-val or verdict not = 0
        set address of expr-arena to expr-ptr
        if expr-kind(current-id) not = 5 or p = 0 move 1 to verdict goback end-if
        move expr-b(current-id) to body-id
        set address of list-arena to list-ptr move list-a(p) to fv move list-b(p) to p
        call 'expr-instantiate1' using kernel-state body-id fv current-id
    end-perform
    move current-id to result-expr
    goback.
end program nested-apply-params.

identification division.
program-id. expr-remap-locals.
data division.
local-storage section.
01 vector-ptr usage pointer.
01 vector-cap binary-long unsigned.
01 vector-count binary-long unsigned.
01 width binary-long unsigned value 8.
01 abstracted binary-long unsigned.
01 p binary-long unsigned.
01 i binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'list.cpy'.
01 input-expr binary-long unsigned.
01 from-list binary-long unsigned.
01 to-list binary-long unsigned.
01 result-expr binary-long unsigned.
01 vector-data based.
   02 vector-entry occurs 1 to 67108864 depending on vector-cap.
      03 vector-key binary-long unsigned.
      03 vector-value binary-long unsigned.
procedure division using kernel-state input-expr from-list to-list result-expr.
    move input-expr to result-expr
    if verdict not = 0 goback end-if
    if from-list = 0 or to-list = 0
        if from-list not = to-list move 3 to verdict end-if
        goback
    end-if
    set address of list-arena to list-ptr
    move list-length(from-list) to vector-count
    if list-length(to-list) not = vector-count move 3 to verdict goback end-if
    call 'arena-reserve' using vector-ptr vector-cap vector-count width verdict
    if verdict not = 0 goback end-if
    set address of vector-data to vector-ptr
    move from-list to p
    perform varying i from 1 by 1 until i > vector-count
        move list-a(p) to vector-value(i) move list-b(p) to p
    end-perform
    call 'expr-abstract' using kernel-state input-expr vector-count vector-ptr abstracted
    set address of list-arena to list-ptr move to-list to p
    perform varying i from 1 by 1 until i > vector-count
        move list-a(p) to vector-value(i) move list-b(p) to p
    end-perform
    call 'expr-instantiate-rev' using kernel-state abstracted vector-count vector-ptr result-expr
    call 'arena-release' using vector-ptr
    goback.
end program expr-remap-locals.

identification division.
program-id. name-reprefix recursive.
data division.
local-storage section.
01 prefix-id binary-long unsigned.
01 new-prefix binary-long unsigned.
01 kind-id binary-long unsigned.
01 number-val binary-double unsigned.
01 text-length binary-long unsigned.
01 buffer-ptr usage pointer.
01 buffer-length binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'names.cpy'.
01 input-name binary-long unsigned.
01 old-prefix binary-long unsigned.
01 replacement binary-long unsigned.
01 result-name binary-long unsigned.
01 buffer-text based.
   02 buffer-byte pic x occurs 1 to 2000000000 depending on buffer-length.
procedure division using kernel-state input-name old-prefix replacement result-name.
    move input-name to result-name
    if verdict not = 0 goback end-if
    if input-name = old-prefix move replacement to result-name goback end-if
    set address of name-arena to name-ptr
    if name-kind(input-name) = 0 goback end-if
    move name-pre(input-name) to prefix-id
    call 'name-reprefix' using kernel-state prefix-id old-prefix replacement new-prefix
    if verdict not = 0 or new-prefix = prefix-id goback end-if
    set address of name-arena to name-ptr
    move name-kind(input-name) to kind-id move name-number(input-name) to number-val
    move name-length(input-name) to text-length
    compute buffer-length = function max(1, text-length)
    allocate buffer-length characters returning buffer-ptr
    if buffer-ptr = null move 2 to verdict goback end-if
    set address of buffer-text to buffer-ptr set address of string-bytes to byte-ptr
    if text-length > 0 move string-bytes(name-start(input-name):text-length) to buffer-text(1:text-length) end-if
    call 'name-intern' using kernel-state kind-id new-prefix number-val buffer-text text-length result-name
    free buffer-ptr
    goback.
end program name-reprefix.

identification division.
program-id. name-index-after-raw.
data division.
local-storage section.
01 prefix-id binary-long unsigned.
01 text-length binary-long unsigned.
01 base-length binary-long unsigned.
01 digits pic Z(9)9.
01 suffix pic x(11).
01 suffix-length binary-long unsigned.
01 buffer-ptr usage pointer.
01 buffer-length binary-long unsigned.
01 kind-id binary-long unsigned value 1.
01 number-val binary-double unsigned.
linkage section.
copy 'state.cpy'.
copy 'names.cpy'.
01 input-name binary-long unsigned.
01 index-val binary-long unsigned.
01 result-name binary-long unsigned.
01 buffer-text based.
   02 buffer-byte pic x occurs 1 to 2000000000 depending on buffer-length.
procedure division using kernel-state input-name index-val result-name.
    move 0 to result-name
    if verdict not = 0 goback end-if
    move index-val to digits
    move spaces to suffix
    string '_' function trim(digits) into suffix end-string
    move function length(function trim(suffix)) to suffix-length
    set address of name-arena to name-ptr
    if name-kind(input-name) = 1
        move name-pre(input-name) to prefix-id move name-length(input-name) to base-length
    else move input-name to prefix-id end-if
    move base-length to text-length
    add suffix-length to text-length
    move text-length to buffer-length
    allocate buffer-length characters returning buffer-ptr
    if buffer-ptr = null move 2 to verdict goback end-if
    set address of buffer-text to buffer-ptr set address of string-bytes to byte-ptr
    if base-length > 0 move string-bytes(name-start(input-name):base-length) to buffer-text(1:base-length) end-if
    move suffix(1:suffix-length) to buffer-text(base-length + 1:suffix-length)
    call 'name-intern' using kernel-state kind-id prefix-id number-val buffer-text text-length result-name
    free buffer-ptr
    goback.
end program name-index-after-raw.

*> Name.modifyBase preserves hygienic macro scopes around the changed base.
identification division.
program-id. name-index-after.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 base-id binary-long unsigned.
01 new-base binary-long unsigned.
01 scopes binary-long unsigned.
01 anonymous-name binary-long unsigned value 1.
linkage section.
copy 'state.cpy'.
copy 'names.cpy'.
01 input-name binary-long unsigned.
01 index-val binary-long unsigned.
01 result-name binary-long unsigned.
procedure division using kernel-state input-name index-val result-name.
    move 0 to result-name
    if verdict not = 0 goback end-if
    move input-name to current-id
    set address of name-arena to name-ptr set address of string-bytes to byte-ptr
    perform until name-kind(current-id) not = 2
        add 1 to scopes move name-pre(current-id) to current-id
    end-perform
    if name-kind(current-id) not = 1
        call 'name-index-after-raw' using kernel-state input-name index-val result-name goback
    end-if
    if name-length(current-id) not = 4
        call 'name-index-after-raw' using kernel-state input-name index-val result-name goback
    end-if
    if string-bytes(name-start(current-id):4) not = '_hyg'
        call 'name-index-after-raw' using kernel-state input-name index-val result-name goback
    end-if
    move name-pre(current-id) to current-id
    perform until name-kind(current-id) = 0
        if name-kind(current-id) = 1 and name-length(current-id) = 2
            if string-bytes(name-start(current-id):2) = '_@'
                move name-pre(current-id) to base-id exit perform
            end-if
        end-if
        move name-pre(current-id) to current-id
    end-perform
    if base-id = 0
        *> Lean's malformed hygienic-name panic returns the default view.
        call 'name-index-after-raw' using kernel-state anonymous-name index-val result-name goback
    end-if
    call 'name-index-after-raw' using kernel-state base-id index-val new-base
    if scopes = 0 move new-base to result-name goback end-if
    call 'name-reprefix' using kernel-state input-name base-id new-base result-name
    goback.
end program name-index-after.
