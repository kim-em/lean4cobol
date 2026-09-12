*> EquivManager: structural alpha comparison augmented by union/find of pairs
*> already proved definitionally equal. Cache families 7 and 8 hold parent/rank.
identification division.
program-id. equiv-root.
data division.
local-storage section.
01 current-id binary-long unsigned.
01 parent-id binary-long unsigned.
01 root-id binary-long unsigned.
01 family binary-long unsigned value 7.
01 zero-val binary-long unsigned.
01 ignored binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 result-id binary-long unsigned.
procedure division using kernel-state input-expr result-id.
    move input-expr to current-id
    perform until verdict not = 0
        call 'tc-cache' using kernel-state family current-id zero-val zero-val parent-id
        if parent-id = 0 or parent-id = current-id exit perform end-if
        move parent-id to current-id
    end-perform
    move current-id to result-id root-id
    move input-expr to current-id
    perform until current-id = root-id or verdict not = 0
        call 'tc-cache' using kernel-state family current-id zero-val zero-val parent-id
        call 'tc-cache' using kernel-state family current-id zero-val root-id ignored
        move parent-id to current-id
    end-perform
    goback.
end program equiv-root.

identification division.
program-id. equiv-merge.
data division.
local-storage section.
01 lroot binary-long unsigned.
01 rroot binary-long unsigned.
01 lrank binary-long unsigned.
01 rrank binary-long unsigned.
01 parent-family binary-long unsigned value 7.
01 rank-family binary-long unsigned value 8.
01 zero-val binary-long unsigned.
01 ignored binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
procedure division using kernel-state lhs rhs.
    if verdict not = 0 goback end-if
    call 'equiv-root' using kernel-state lhs lroot
    call 'equiv-root' using kernel-state rhs rroot
    if lroot = rroot goback end-if
    call 'tc-cache' using kernel-state rank-family lroot zero-val zero-val lrank
    call 'tc-cache' using kernel-state rank-family rroot zero-val zero-val rrank
    if lrank < rrank
        call 'tc-cache' using kernel-state parent-family lroot zero-val rroot ignored
    else
        call 'tc-cache' using kernel-state parent-family rroot zero-val lroot ignored
        if lrank = rrank
            add 1 to lrank
            call 'tc-cache' using kernel-state rank-family lroot zero-val lrank ignored
        end-if
    end-if
    goback.
end program equiv-merge.

identification division.
program-id. equiv-test recursive.
data division.
local-storage section.
01 lk binary-long unsigned.
01 rk binary-long unsigned.
01 la binary-long unsigned.
01 lb binary-long unsigned.
01 lc binary-long unsigned.
01 ra binary-long unsigned.
01 rb binary-long unsigned.
01 rc binary-long unsigned.
01 lroot binary-long unsigned.
01 rroot binary-long unsigned.
01 next-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'expr.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 use-hash binary-char unsigned.
01 depth-val binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs use-hash depth-val answer.
    move 0 to answer
    if verdict not = 0 goback end-if
    if lhs = rhs move 1 to answer goback end-if
    if depth-val >= recursion-limit move 2 to verdict goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    set address of expr-arena to expr-ptr
    if use-hash = 1 and expr-hash(lhs) not = expr-hash(rhs) goback end-if
    move expr-kind(lhs) to lk move expr-kind(rhs) to rk
    move expr-a(lhs) to la move expr-b(lhs) to lb move expr-c(lhs) to lc
    move expr-a(rhs) to ra move expr-b(rhs) to rb move expr-c(rhs) to rc
    if lk = 0 and rk = 0
        if la = ra move 1 to answer end-if goback
    end-if
    call 'equiv-root' using kernel-state lhs lroot
    call 'equiv-root' using kernel-state rhs rroot
    if lroot = rroot move 1 to answer goback end-if
    if lk not = rk goback end-if
    evaluate lk
      when 1 when 8 when 9 when 10
        if la = ra move 1 to answer end-if
      when 2 if la = ra and lb = rb move 1 to answer end-if
      when 3 when 4 when 5 when 6
        call 'equiv-test' using kernel-state la ra use-hash next-depth answer
        if answer = 1 and verdict = 0
            call 'equiv-test' using kernel-state lb rb use-hash next-depth answer
        end-if
        if lk = 6 and answer = 1 and verdict = 0
            call 'equiv-test' using kernel-state lc rc use-hash next-depth answer
        end-if
      when 7
        if lb = rb
            call 'equiv-test' using kernel-state lc rc use-hash next-depth answer
        end-if
      when 11 call 'equiv-test' using kernel-state la ra use-hash next-depth answer
    end-evaluate
    if answer = 1 call 'equiv-merge' using kernel-state lhs rhs end-if
    goback.
end program equiv-test.
