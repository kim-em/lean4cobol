*> FuelConfig.recDepth: only the four Methods entry points consume depth.

identification division.
program-id. infer-type recursive.
data division.
local-storage section.
01 zero-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-expr.
    move 0 to result-expr
    if verdict not = 0 goback end-if
    if tc-method-depth >= fuel-rec-depth move 2 to verdict goback end-if
    add 1 to tc-method-depth
    call 'infer-type-impl' using kernel-state input-expr zero-depth result-expr
    subtract 1 from tc-method-depth
    goback.
end program infer-type.

identification division.
program-id. weak-head recursive.
data division.
local-storage section.
01 zero-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-expr.
    move 0 to result-expr
    if verdict not = 0 goback end-if
    if tc-method-depth >= fuel-rec-depth move 2 to verdict goback end-if
    add 1 to tc-method-depth
    call 'weak-head-body' using kernel-state input-expr zero-depth result-expr
    subtract 1 from tc-method-depth
    goback.
end program weak-head.

identification division.
program-id. weak-head-core-impl recursive.
data division.
local-storage section.
01 zero-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-expr.
    move 0 to result-expr
    if verdict not = 0 goback end-if
    if tc-method-depth >= fuel-rec-depth move 2 to verdict goback end-if
    add 1 to tc-method-depth
    call 'weak-head-core-body' using kernel-state input-expr zero-depth result-expr
    subtract 1 from tc-method-depth
    goback.
end program weak-head-core-impl.

identification division.
program-id. def-equal-core recursive.
data division.
local-storage section.
01 zero-depth binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 depth-val binary-long unsigned.
01 answer binary-char unsigned.
procedure division using kernel-state lhs rhs depth-val answer.
    move 0 to answer
    if verdict not = 0 goback end-if
    if tc-method-depth >= fuel-rec-depth move 2 to verdict goback end-if
    add 1 to tc-method-depth
    call 'def-equal-body' using kernel-state lhs rhs zero-depth answer
    subtract 1 from tc-method-depth
    goback.
end program def-equal-core.

*> whnf' calls whnfCore' directly, without consuming another method unit.
identification division.
program-id. weak-head-core-direct recursive.
data division.
local-storage section.
01 saved-mode binary-char unsigned.
linkage section.
copy 'state.cpy'.
01 input-expr binary-long unsigned.
01 depth-val binary-long unsigned.
01 result-expr binary-long unsigned.
procedure division using kernel-state input-expr depth-val result-expr.
    move tc-cheap-proj to saved-mode move 0 to tc-cheap-proj
    call 'weak-head-core-body' using kernel-state input-expr depth-val result-expr
    move saved-mode to tc-cheap-proj
    goback.
end program weak-head-core-direct.
