identification division.
program-id. primitive-name.
data division.
working-storage section.
01 spellings.
   02 filler pic x(24) value 'Bool'.
   02 filler pic x(24) value 'Bool.false'.
   02 filler pic x(24) value 'Bool.true'.
   02 filler pic x(24) value 'Nat'.
   02 filler pic x(24) value 'Nat.zero'.
   02 filler pic x(24) value 'Nat.succ'.
   02 filler pic x(24) value 'Nat.add'.
   02 filler pic x(24) value 'Nat.pred'.
   02 filler pic x(24) value 'Nat.sub'.
   02 filler pic x(24) value 'Nat.mul'.
   02 filler pic x(24) value 'Nat.pow'.
   02 filler pic x(24) value 'Nat.gcd'.
   02 filler pic x(24) value 'Nat.mod'.
   02 filler pic x(24) value 'Nat.div'.
   02 filler pic x(24) value 'Nat.beq'.
   02 filler pic x(24) value 'Nat.ble'.
   02 filler pic x(24) value 'Nat.bitwise'.
   02 filler pic x(24) value 'Nat.land'.
   02 filler pic x(24) value 'Nat.lor'.
   02 filler pic x(24) value 'Nat.xor'.
   02 filler pic x(24) value 'Nat.shiftLeft'.
   02 filler pic x(24) value 'Nat.shiftRight'.
   02 filler pic x(24) value 'String.ofList'.
   02 filler pic x(24) value 'Char.ofNat'.
01 spelling-table redefines spellings.
   02 spelling pic x(24) occurs 24.
local-storage section.
01 i binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 name-id binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state name-id answer.
    move 0 to answer
    perform varying i from 1 by 1 until i > 24 or verdict not = 0
        call 'name-matches' using kernel-state name-id spelling(i) answer
        if answer = 1 goback end-if
    end-perform
    goback.
end program primitive-name.

identification division.
program-id. check-primitive-ordinary.
data division.
local-storage section.
01 name-id binary-long unsigned.
01 matched binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'declarations.cpy'.
01 declaration-id binary-long unsigned.
procedure division using kernel-state declaration-id.
    if verdict not = 0 goback end-if
    set address of decl-arena to decl-ptr move decl-name(declaration-id) to name-id
    call 'primitive-name' using kernel-state name-id matched
    if matched = 1
        if decl-kind(declaration-id) = 1
            call 'check-primitive-definition' using kernel-state declaration-id
        else move 1 to verdict end-if
    end-if
    goback.
end program check-primitive-ordinary.

identification division.
program-id. ind-primitive-check.
data division.
local-storage section.
01 i binary-long unsigned.
01 d binary-long unsigned.
01 n binary-long unsigned.
01 p binary-long unsigned.
01 c1 binary-long unsigned.
01 c2 binary-long unsigned.
01 ty binary-long unsigned.
01 one-level binary-long unsigned.
01 universe-type binary-long unsigned.
01 ind-const binary-long unsigned.
01 ctor-type binary-long unsigned.
01 zero-val binary-long unsigned.
01 one-val binary-long unsigned value 1.
01 const-kind binary-long unsigned value 2.
01 pi-kind binary-long unsigned value 5.
01 is-bool binary-char unsigned.
01 is-nat binary-char unsigned.
01 matched binary-char unsigned.
linkage section.
copy 'state.cpy'.
copy 'inductive.cpy'.
copy 'inductive-arena.cpy'.
copy 'declarations.cpy'.
copy 'names.cpy'.
copy 'list.cpy'.
procedure division using kernel-state ind-state.
    if verdict not = 0 goback end-if
    set address of ind-arena to ind-ptr move ind-source(1) to d
    set address of decl-arena to decl-ptr move decl-name(d) to n move decl-type(d) to ty
    call 'name-matches' using kernel-state n 'Bool' is-bool
    call 'name-matches' using kernel-state n 'Nat' is-nat
    if ind-count = 1 and ind-lparams = 0 and ind-nparams = 0 and (is-bool = 1 or is-nat = 1)
        call 'level-intern' using kernel-state one-val one-val zero-val one-level
        call 'expr-intern' using kernel-state one-val one-level zero-val zero-val zero-val universe-type
        if ty = universe-type
            set address of ind-arena to ind-ptr move ind-ctors(1) to p
            if p = 0 move 1 to verdict goback end-if
            set address of list-arena to list-ptr
            if list-length(p) not = 2 move 1 to verdict goback end-if
            move list-a(p) to c1 move list-b(p) to p move list-a(p) to c2
            if is-bool = 1
                call 'name-matches' using kernel-state c1 'Bool.false' matched
                if matched = 0 move 1 to verdict goback end-if
                call 'name-matches' using kernel-state c2 'Bool.true' matched
            else
                call 'name-matches' using kernel-state c1 'Nat.zero' matched
                if matched = 0 move 1 to verdict goback end-if
                call 'name-matches' using kernel-state c2 'Nat.succ' matched
            end-if
            if matched = 0 move 1 to verdict goback end-if
            call 'expr-intern' using kernel-state const-kind n zero-val zero-val zero-val ind-const
            set address of name-arena to name-ptr move name-decl(c1) to d
            set address of decl-arena to decl-ptr
            if decl-type(d) not = ind-const move 1 to verdict goback end-if
            move ind-const to ctor-type
            if is-nat = 1
                call 'expr-intern' using kernel-state pi-kind ind-const ind-const zero-val zero-val ctor-type
            end-if
            set address of name-arena to name-ptr move name-decl(c2) to d
            set address of decl-arena to decl-ptr
            if decl-type(d) not = ctor-type move 1 to verdict goback end-if
            move 1 to ind-allow-primitive
        end-if
    end-if
    if ind-allow-primitive = 1 goback end-if
    perform varying i from 1 by 1 until i > ind-count or verdict not = 0
        set address of ind-arena to ind-ptr move ind-source(i) to d move ind-ctors(i) to p
        set address of decl-arena to decl-ptr move decl-name(d) to n
        call 'primitive-name' using kernel-state n matched
        if matched = 1 move 1 to verdict goback end-if
        perform until p = 0 or verdict not = 0
            set address of list-arena to list-ptr move list-a(p) to n move list-b(p) to p
            call 'primitive-name' using kernel-state n matched
            if matched = 1 move 1 to verdict goback end-if
        end-perform
    end-perform
    goback.
end program ind-primitive-check.
