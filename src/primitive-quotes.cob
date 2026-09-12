*> Fixed expression quotations extracted from the pinned Primitive.lean.
*> Every instruction and quote name is compiled into the checker. Context
*> holes carry already-built expressions; no input-stream text is evaluated.
identification division.
program-id. reflection-quote.
data division.
local-storage section.
copy 'quote-cache.cpy'.
01 root-id binary-long unsigned.
linkage section.
copy 'state.cpy'.
copy 'reflection.cpy'.
01 quotation-name pic x any length.
01 result-expr binary-long unsigned.
procedure division using kernel-state reflection-context quotation-name result-expr.
    move 0 to result-expr
    if verdict not = 0 goback end-if
    copy 'quote-select.cpy'.
    if verdict not = 0 goback end-if
    call 'reflection-quote-node' using kernel-state reflection-context quote-cache root-id result-expr
    goback.
end program reflection-quote.

identification division.
program-id. reflection-quote-node recursive.
data division.
working-storage section.
copy 'quote-data.cpy'.
local-storage section.
01 i binary-long unsigned.
01 bit-value binary-long unsigned value 1.
01 k binary-long unsigned.
01 mask-val binary-long unsigned.
01 child-id binary-long unsigned.
01 arguments.
   02 arg-val binary-long unsigned occurs 4.
linkage section.
copy 'state.cpy'.
copy 'reflection.cpy'.
copy 'quote-cache.cpy'.
01 node-id binary-long unsigned.
01 result-id binary-long unsigned.
procedure division using kernel-state reflection-context quote-cache node-id result-id.
    move 0 to result-id
    if verdict not = 0 or node-id = 0 goback end-if
    if quote-memo(node-id) not = 0 move quote-memo(node-id) to result-id goback end-if
    move quote-kind(node-id) to k move quote-mask(node-id) to mask-val
    perform varying i from 1 by 1 until i > 4 or verdict not = 0
        move quote-arg(node-id, i) to child-id
        if function mod(function integer(mask-val / bit-value), 2) = 1
            call 'reflection-quote-node' using kernel-state reflection-context quote-cache child-id arg-val(i)
        else move child-id to arg-val(i) end-if
        multiply 2 by bit-value
    end-perform
    if verdict not = 0 goback end-if
    evaluate quote-family(node-id)
      when 'N' call 'builtin-name' using kernel-state quote-text(node-id) result-id
      when 'L' call 'level-intern' using kernel-state k arg-val(1) arg-val(2) result-id
      when 'S' call 'list-intern' using kernel-state arg-val(1) arg-val(2) result-id
      when 'B' call 'blob-intern' using kernel-state quote-text(node-id) arg-val(1) result-id
      when 'E' call 'expr-intern' using kernel-state k arg-val(1) arg-val(2) arg-val(3) arg-val(4) result-id
      when 'H'
        move reflection-slot(arg-val(1)) to result-id
        if result-id = 0 move 3 to verdict end-if
      when other move 3 to verdict
    end-evaluate
    move result-id to quote-memo(node-id)
    goback.
end program reflection-quote-node.
