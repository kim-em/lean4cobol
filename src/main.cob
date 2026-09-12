identification division.
program-id. lean4cobol.
data division.
working-storage section.
copy 'state.cpy'.
copy 'stream.cpy'.
copy 'parser-state.cpy'.
copy 'json.cpy'.
01 input-path pic x(4096).
01 argument-text pic x(4096).
01 argument-count binary-long unsigned.
01 argument-index binary-long unsigned.
01 scan-only binary-char unsigned.
01 have-path binary-char unsigned.
01 declaration-id binary-long unsigned.
01 zero-depth binary-long unsigned.
01 display-count pic Z(19)9.
01 progress-option pic x.
01 next-progress binary-double unsigned value 1000000.
procedure division.
    call 'kernel-init' using kernel-state
    accept progress-option from environment 'LEAN4COBOL_PROGRESS'
        on exception move space to progress-option
    end-accept
    accept argument-count from argument-number
    perform varying argument-index from 1 by 1
        until argument-index > argument-count
        accept argument-text from argument-value
        evaluate function trim(argument-text)
          when '--scan' move 1 to scan-only
          when '--help'
            display 'usage: lean4cobol [--scan] FILE'
            stop run returning 0
          when other
            if have-path = 1
                display 'expected one input file' upon syserr
                stop run returning 3
            end-if
            move argument-text to input-path
            move 1 to have-path
        end-evaluate
    end-perform
    if have-path = 0
        display 'usage: lean4cobol [--scan] FILE' upon syserr
        stop run returning 3
    end-if
    call 'stream-open' using stream-state input-path verdict
    perform until verdict not = 0
        call 'stream-next' using stream-state json-input json-length
            verdict
        if verdict not = 0 or stream-eof = 1 exit perform end-if
        perform process-record
    end-perform
    call 'stream-close' using stream-state verdict
    if verdict = 0 and seen-meta = 0 move 1 to verdict end-if
    if verdict = 0 and scan-only = 0 and pending-declarations = 1
        move 1 to verdict
    end-if
    if verdict = 0 and scan-only = 0
        if progress-option = '1'
            display 'parse complete: records=' record-count
                ' exprs=' expr-count ' declarations=' decl-count upon syserr
        end-if
        call 'replay-run' using kernel-state
    end-if
    move record-count to display-count
    display 'records=' function trim(display-count) with no advancing
    move name-count to display-count
    display ' names=' function trim(display-count) with no advancing
    move level-count to display-count
    display ' levels=' function trim(display-count) with no advancing
    move expr-count to display-count
    display ' exprs=' function trim(display-count) with no advancing
    move longest-record to display-count
    display ' longest=' function trim(display-count)
    evaluate verdict
      when 0
        if scan-only = 1 display 'scan complete (no proof checking)'
        else display 'accepted' end-if
      when 1 display 'rejected at record ' record-count upon syserr
      when 2 display 'declined: unsupported feature or resource limit'
        upon syserr
      when other display 'checker error' upon syserr
    end-evaluate
    if json-ptr not = null call 'arena-release' using json-ptr end-if
    if map-ptr not = null call 'arena-release' using map-ptr end-if
    perform varying argument-index from 1 by 1 until argument-index > 3
        call 'arena-release' using dense-ptr(argument-index)
    end-perform
    call 'kernel-free' using kernel-state
    stop run returning verdict.
process-record.
    add 1 to record-count
    compute longest-record = function max(longest-record, json-length)
    call 'parser-record' using kernel-state parser-state json-state
    if progress-option = '1' and record-count >= next-progress
        display 'parsed records=' record-count ' exprs=' expr-count upon syserr
        add 1000000 to next-progress
    end-if
    move 0 to json-length.
end program lean4cobol.
