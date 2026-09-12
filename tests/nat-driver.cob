identification division.
program-id. nat-test.
environment division.
input-output section.
file-control.
    select input-stream assign to '/dev/stdin'
        organization is line sequential.
data division.
file section.
fd input-stream.
01 input-line pic x(100000).
working-storage section.
copy 'state.cpy'.
01 op-text pic x(2).
01 lhs-text pic x(33000).
01 rhs-text pic x(33000).
01 expected-text pic x(33000).
01 operation binary-long unsigned.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 expected binary-long unsigned.
01 actual binary-long unsigned.
01 text-size binary-long unsigned.
01 tests-run binary-long unsigned.
procedure division.
    open input input-stream
    call 'kernel-init' using kernel-state
    perform until verdict not = 0
        move spaces to input-line
        read input-stream at end move spaces to input-line end-read
        if input-line = spaces exit perform end-if
        move spaces to op-text lhs-text rhs-text expected-text
        unstring input-line delimited by all spaces into op-text lhs-text rhs-text expected-text
        compute operation = function numval(op-text)
        compute text-size = function length(function trim(lhs-text))
        call 'blob-intern' using kernel-state lhs-text text-size lhs
        compute text-size = function length(function trim(rhs-text))
        call 'blob-intern' using kernel-state rhs-text text-size rhs
        compute text-size = function length(function trim(expected-text))
        call 'blob-intern' using kernel-state expected-text text-size expected
        call 'bignum-calc' using kernel-state operation lhs rhs actual
        add 1 to tests-run
        if expected-text = 'decline' and verdict = 2
            move 0 to verdict
        else
            if verdict not = 0 or actual not = expected
                display 'Nat arithmetic failure at case ' tests-run ': ' function trim(input-line)
                display 'verdict=' verdict ' actual blob=' actual ' expected blob=' expected
                move 1 to verdict
            end-if
        end-if
    end-perform
    display tests-run ' Nat arithmetic checks'
    close input-stream
    call 'kernel-free' using kernel-state
    move verdict to return-code goback.
end program nat-test.
