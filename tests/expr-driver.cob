identification division.
program-id. expr-test.
data division.
working-storage section.
copy 'state.cpy'.
copy 'transform.cpy'.
01 input-line pic x(4096).
01 operation pic x.
01 seq-id binary-long unsigned.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 arg-c-val binary-long unsigned.
01 arg-d-val binary-long unsigned.
01 result-id binary-long unsigned.
01 number-val binary-long unsigned.
01 eq-answer binary-char unsigned.
01 test-count binary-long unsigned.
01 field-count binary-long unsigned.
01 field-index binary-long unsigned.
01 i binary-long unsigned.
01 zero-depth binary-long unsigned.
01 saved-limit binary-long unsigned.
01 words-table.
   02 word-val pic x(30) occurs 200.
01 ids.
   02 expr-map binary-long unsigned occurs 1000000.
   02 level-map binary-long unsigned occurs 1000000.
   02 list-map binary-long unsigned occurs 1000000.
01 vector-context.
   02 vector-count binary-long unsigned.
   02 vector-entries.
      03 vector-entry occurs 64.
         04 vector-key binary-long unsigned.
         04 vector-val binary-long unsigned.
linkage section.
copy 'expr.cpy'.
procedure division.
    call 'kernel-init' using kernel-state
    move 1 to level-map(1)
    perform until verdict not = 0
        move spaces to input-line words-table
        accept input-line
        if input-line = spaces exit perform end-if
        move 1 to field-index
        move 0 to field-count
        perform until field-index > function length(function trim(input-line))
            add 1 to field-count
            unstring input-line delimited by all spaces into
                word-val(field-count) with pointer field-index
            end-unstring
        end-perform
        move word-val(1) to operation
        compute seq-id = function numval(word-val(2))
        compute k = function numval(word-val(3))
        compute a = function numval(word-val(4))
        compute b = function numval(word-val(5))
        compute arg-c-val = function numval(word-val(6))
        compute arg-d-val = function numval(word-val(7))
        evaluate operation
          when 'L'
            if k not = 4 move level-map(a + 1) to a end-if
            if k = 2 or 3 move level-map(b + 1) to b else move 0 to b end-if
            call 'level-intern' using kernel-state k a b result-id
            move result-id to level-map(seq-id + 1)
          when 'S'
            move list-map(a + 1) to b
            move level-map(k + 1) to a
            call 'list-intern' using kernel-state a b result-id
            move result-id to list-map(seq-id + 1)
          when 'E'
            evaluate k
              when 1 move level-map(a + 1) to a
              when 2 move list-map(b + 1) to b
              when 3 when 4 when 5
                move expr-map(a + 1) to a
                move expr-map(b + 1) to b
              when 6
                move expr-map(a + 1) to a
                move expr-map(b + 1) to b
                move expr-map(arg-c-val + 1) to arg-c-val
              when 7 move expr-map(arg-c-val + 1) to arg-c-val
              when 11 move expr-map(a + 1) to a
            end-evaluate
            call 'expr-intern' using kernel-state k a b arg-c-val
                arg-d-val result-id
            move result-id to expr-map(seq-id + 1)
          when 'T'
            move k to tx-mode move b to tx-amount
            move arg-c-val to tx-count vector-count
            move expr-map(a + 1) to a
            perform varying i from 1 by 1 until i > tx-count
                compute vector-key(i) = function numval(word-val(6 + 2 * i))
                compute number-val = function numval(word-val(7 + 2 * i))
                if tx-mode = 4
                    move level-map(number-val + 1) to vector-val(i)
                else
                    move expr-map(number-val + 1) to vector-val(i)
                end-if
                if tx-mode = 5
                    move expr-map(vector-key(i) + 1) to vector-key(i)
                end-if
            end-perform
            set tx-values to address of vector-entries
            set tx-context to address of vector-context
            move 'expr-test-replace' to tx-callback
            evaluate tx-mode
              when 0 call 'expr-lift' using kernel-state a tx-amount result-id
              when 1 call 'expr-instantiate' using kernel-state a tx-count tx-values result-id
              when 2 call 'expr-instantiate-rev' using kernel-state a tx-count tx-values result-id
              when 3 call 'expr-abstract' using kernel-state a tx-count tx-values result-id
              when 4 call 'expr-level-params' using kernel-state a tx-count tx-values result-id
              when 5 call 'expr-replace' using kernel-state a tx-callback tx-context result-id
              when 6 call 'expr-abstract-range' using kernel-state a tx-amount tx-count tx-values result-id
              when 7 call 'expr-instantiate1' using kernel-state a vector-val(1) result-id
              when 9 call 'expr-cheap-beta' using kernel-state a result-id
              when 8
                move a to result-id
                call 'expr-instantiate1' using kernel-state result-id vector-val(1) result-id
              when other move 3 to verdict
            end-evaluate
            move result-id to expr-map(seq-id + 1)
          when 'C'
            call 'expr-eqv' using expr-map(k + 1) expr-map(a + 1) eq-answer
            if eq-answer not = 1 perform failed end-if
            add 1 to test-count
          when 'Y'
            call 'tc-cache-free' using kernel-state initialize tc-context
            move 100000 to fuel-whnf move 1000000 to fuel-whnf-eager
            if field-count >= 10
                compute fuel-whnf = function numval(word-val(8))
                compute fuel-whnf-eager = function numval(word-val(9))
                compute tc-eager = function numval(word-val(10))
            end-if
            move fuel-rec-depth to saved-limit
            move expr-map(a + 1) to a move expr-map(b + 1) to b
            if k > 10
                subtract 10 from k
                move 50000 to fuel-rec-depth
                perform method-call
                if verdict not = 0 perform failed end-if
            end-if
            move arg-c-val to fuel-rec-depth
            perform method-call
            if verdict = arg-d-val and tc-method-depth = 0
                move 0 to verdict
                if arg-d-val = 0
                    if k = 5
                        if eq-answer not = 1 perform failed end-if
                    else
                        if result-id not = b perform failed end-if
                    end-if
                end-if
            else perform failed end-if
            move saved-limit to fuel-rec-depth
            add 1 to test-count
          when 'F' move k to recursion-limit
          when 'D'
            set address of expr-arena to expr-ptr
            move expr-map(k + 1) to result-id
            if expr-lbvr(result-id) not = a or
                expr-has-fvar(result-id) not = b or
                expr-has-param(result-id) not = arg-c-val
                perform failed
            end-if
            add 1 to test-count
          when other move 3 to verdict
        end-evaluate
    end-perform
    display 'expression checks: ' test-count
    call 'kernel-free' using kernel-state
    stop run returning verdict.
method-call.
    evaluate k
      when 1 call 'infer-type' using kernel-state a zero-depth result-id
      when 2 call 'infer-only' using kernel-state a zero-depth result-id
      when 3 call 'weak-head' using kernel-state a zero-depth result-id
      when 4 call 'weak-head-core' using kernel-state a zero-depth result-id
      when 5 call 'def-equal' using kernel-state a a zero-depth eq-answer
    end-evaluate.
failed.
    display 'FAIL ' function trim(input-line)
    move 1 to verdict.
end program expr-test.

identification division.
program-id. expr-test-replace.
data division.
local-storage section.
01 i binary-long unsigned.
linkage section.
copy 'state.cpy'.
01 context-ptr usage pointer.
01 input-expr binary-long unsigned.
01 result-expr binary-long unsigned.
01 context-data based.
   02 pair-count binary-long unsigned.
   02 pair-entry occurs 64.
      03 pair-key binary-long unsigned.
      03 pair-value binary-long unsigned.
procedure division using kernel-state context-ptr input-expr result-expr.
    move 0 to result-expr
    set address of context-data to context-ptr
    perform varying i from 1 by 1 until i > pair-count
        if pair-key(i) = input-expr
            move pair-value(i) to result-expr goback
        end-if
    end-perform
    goback.
end program expr-test-replace.
