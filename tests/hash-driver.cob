identification division.
program-id. hash-test.
data division.
working-storage section.
copy 'hash-native.cpy'.
01 input-line pic x(100).
01 seed-text pic 9(10).
01 word-text pic 9(10).
01 result-text pic 9(10).
procedure division.
    perform forever
        move spaces to input-line
        accept input-line
        if input-line = spaces exit perform end-if
        unstring input-line delimited by space into seed-text word-text
        move seed-text to hash-acc
        move word-text to hash-input
        perform hash-mix
        move hash-acc to result-text
        display result-text
    end-perform
    goback.
copy 'hash-mix.cpy'.
end program hash-test.
