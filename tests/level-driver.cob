identification division.
program-id. level-test.
environment division.
configuration section.
repository. function all intrinsic.
data division.
working-storage section.
copy 'state.cpy'.
01 input-line pic x(100).
01 operation pic x.
01 seq-id binary-long unsigned.
01 k binary-long unsigned.
01 a binary-long unsigned.
01 b binary-long unsigned.
01 c binary-long unsigned.
01 out-id binary-long unsigned.
01 expect-val binary-long unsigned.
01 got binary-char unsigned.
01 test-count binary-long unsigned.
01 mapping.
   02 node-map binary-long unsigned occurs 1000000.
procedure division.
    call 'kernel-init' using kernel-state
    move 1 to node-map(1)
    perform until verdict not = 0
        move spaces to input-line
        accept input-line
        if input-line = spaces exit perform end-if
        unstring input-line delimited by all spaces into
            operation seq-id k a b expect-val
        end-unstring
        evaluate operation
          when 'N'
            if k not = 4 move node-map(a + 1) to a end-if
            if k = 2 or k = 3 move node-map(b + 1) to b
            else move 0 to b end-if
            call 'level-intern' using kernel-state k a b out-id
            move out-id to node-map(seq-id + 1)
          when 'C' when 'E'
            move node-map(a + 1) to a
            move node-map(b + 1) to b
                    if operation = 'E'
                call 'level-native-equal' using kernel-state a b got
            else
                call 'level-compare' using kernel-state a b k got
            end-if
            if verdict = 0 and got not = expect-val
                display 'FAIL ' function trim(input-line)
                    ' got ' got
                move 1 to verdict
            end-if
            add 1 to test-count
          when other move 3 to verdict
        end-evaluate
    end-perform
    display 'level comparisons: ' test-count
    call 'kernel-free' using kernel-state
    move verdict to return-code
    goback.
