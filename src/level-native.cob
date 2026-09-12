*> Native Lean.Level.normalize/isEquiv, distinct from Lean4Lean's complete
*> conditional-sublevel comparison. Interned base handles provide a stable
*> total order for max terms; the choice of order does not change equality.
identification division.
program-id. level-native-equal.
data division.
local-storage section.
01 ln binary-long unsigned.
01 rn binary-long unsigned.
01 depth-val binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs answer.
    move 0 to answer
    if verdict not = 0 goback end-if
    if lhs = rhs move 1 to answer goback end-if
    call 'level-native-normalize' using kernel-state lhs depth-val ln
    call 'level-native-normalize' using kernel-state rhs depth-val rn
    if verdict = 0 and ln = rn move 1 to answer end-if
    goback.
end program level-native-equal.

identification division.
program-id. level-native-normalize recursive.
data division.
local-storage section.
01 original-id binary-long unsigned.
01 base-id binary-long unsigned.
01 offset-val binary-long unsigned.
01 kind-id binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 an binary-long unsigned.
01 bn binary-long unsigned.
01 nn binary-long unsigned.
01 tmp binary-long unsigned.
01 next-depth binary-long unsigned.
01 zero-val binary-long unsigned.
01 max-kind binary-long unsigned value 2.
01 imax-kind binary-long unsigned value 3.
01 i binary-long unsigned.
01 j binary-long unsigned.
01 term-base binary-long unsigned.
01 term-offset binary-long unsigned.
01 max-offset binary-long unsigned.
01 terms-state.
   02 terms-ptr usage pointer.
   02 terms-cap binary-long unsigned.
   02 terms-count binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'levels.cpy'.
01 input-level binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-level binary-long unsigned.
01 terms-data based.
   02 term-entry occurs 1 to 67108864 depending on terms-count.
      03 term-key binary-long unsigned.
      03 term-value binary-long unsigned.
procedure division using kernel-state input-level depth-val result-level.
    move input-level to original-id result-level
    if verdict not = 0 goback end-if
    set address of level-arena to level-ptr
    if level-native-normal(original-id) not = 0
        move level-native-normal(original-id) to result-level goback
    end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    move level-base(original-id) to base-id
    move level-offset(original-id) to offset-val
    move level-kind(base-id) to kind-id
    move level-a(base-id) to a move level-b(base-id) to b
    evaluate kind-id
      when 0 when 4 move original-id to nn
      when 2
        call 'level-native-normalize' using kernel-state a next-depth an
        call 'level-native-normalize' using kernel-state b next-depth bn
        perform normalize-max
      when 3
        if level-never-zero(b) = 1
            call 'level-intern' using kernel-state max-kind a b tmp
            call 'level-native-normalize' using kernel-state tmp next-depth an
            call 'level-add-offset' using kernel-state an offset-val nn
        else
            call 'level-native-normalize' using kernel-state a next-depth an
            call 'level-native-normalize' using kernel-state b next-depth bn
            if verdict not = 0 goback end-if
            set address of level-arena to level-ptr
            evaluate true
              when level-kind(bn) = 0 move bn to tmp
              when level-base(an) = 1 and level-offset(an) <= 1 move bn to tmp
              when an = bn move an to tmp
              when other
                call 'level-intern' using kernel-state imax-kind an bn tmp
            end-evaluate
            call 'level-add-offset' using kernel-state tmp offset-val nn
        end-if
      when other move 3 to verdict
    end-evaluate
    if terms-ptr not = null call 'arena-release' using terms-ptr end-if
    if verdict = 0
        set address of level-arena to level-ptr
        move nn to level-native-normal(original-id) result-level
    end-if
    goback.
normalize-max.
    call 'level-max-collect' using kernel-state terms-state an next-depth
    call 'level-max-collect' using kernel-state terms-state bn next-depth
    if verdict not = 0 exit paragraph end-if
    set address of terms-data to terms-ptr
    sort term-entry on ascending key term-key term-value
    perform varying i from 1 by 1 until i > terms-count
        if term-key(i) not = 1
            compute max-offset = function max(max-offset, term-value(i))
        end-if
    end-perform
    move 1 to nn i
    perform until i > terms-count or verdict not = 0
        move term-key(i) to term-base
        move term-value(i) to term-offset
        move i to j
        add 1 to j
        perform until j > terms-count
            if term-key(j) not = term-base exit perform end-if
            compute term-offset = function max(term-offset, term-value(j))
            add 1 to j
        end-perform
        if term-base not = 1 or term-offset > max-offset
            add offset-val to term-offset
            call 'level-add-offset' using kernel-state term-base term-offset tmp
            if nn = 1 move tmp to nn
            else
                call 'level-intern' using kernel-state max-kind nn tmp an
                move an to nn
            end-if
        end-if
        move j to i
    end-perform
    *> max 0 0, including outer successors, has no emitted nonzero term.
    if nn = 1
        call 'level-add-offset' using kernel-state nn offset-val tmp
        move tmp to nn
    end-if.
end program level-native-normalize.

identification division.
program-id. level-max-collect recursive.
data division.
local-storage section.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 next-depth binary-long unsigned.
01 wanted binary-long unsigned.
01 width binary-long unsigned value 8.
linkage section.
copy 'state.cpy'.
copy 'levels.cpy'.
01 terms-state.
   02 terms-ptr usage pointer.
   02 terms-cap binary-long unsigned.
   02 terms-count binary-long unsigned.
01 input-level binary-long unsigned.
01 depth-val binary-long unsigned.
01 terms-data based.
   02 term-entry occurs 1 to 67108864 depending on terms-cap.
      03 term-key binary-long unsigned.
      03 term-value binary-long unsigned.
procedure division using kernel-state terms-state input-level depth-val.
    if verdict not = 0 goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    set address of level-arena to level-ptr
    if level-kind(input-level) = 2
        move level-a(input-level) to a move level-b(input-level) to b
        move depth-val to next-depth
        add 1 to next-depth
        call 'level-max-collect' using kernel-state terms-state a next-depth
        call 'level-max-collect' using kernel-state terms-state b next-depth
    else
        move terms-count to wanted
        add 1 to wanted
        call 'arena-reserve' using terms-ptr terms-cap wanted width verdict
        if verdict not = 0 goback end-if
        set address of terms-data to terms-ptr
        add 1 to terms-count
        move level-base(input-level) to term-key(terms-count)
        move level-offset(input-level) to term-value(terms-count)
    end-if
    goback.
end program level-max-collect.

identification division.
program-id. level-add-offset.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 next-id binary-long unsigned.
01 i binary-long unsigned.
01 one-val binary-long unsigned value 1.
01 zero-val binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 input-level binary-long unsigned.
01 offset-val binary-long unsigned.
01 result-level binary-long unsigned.
procedure division using kernel-state input-level offset-val result-level.
    move input-level to current-id result-level
    perform varying i from 1 by 1 until i > offset-val or verdict not = 0
            call 'level-intern' using kernel-state one-val current-id zero-val next-id
        move next-id to current-id
    end-perform
    move current-id to result-level
    goback.
end program level-add-offset.
