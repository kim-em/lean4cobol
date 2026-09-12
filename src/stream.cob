*> Raw block reads avoid LINE SEQUENTIAL control-byte conversion and its
*> GnuCOBOL 3.2 LS_SPLIT bug at an exact record boundary without a final LF.
*> CBL_* are GnuCOBOL runtime subroutines; newline scanning is COBOL.
identification division.
program-id. stream-open.
data division.
local-storage section.
01 access-mode pic x value x'01'.
01 lock-mode pic x value x'00'.
01 device-mode pic x value x'00'.
01 flags-byte pic x value x'80'.
01 io-result binary-long signed.
linkage section.
copy 'stream.cpy'.
01 file-path pic x any length.
01 status-code binary-long signed.
procedure division using stream-state file-path status-code.
    initialize stream-state
    if status-code not = 0 goback end-if
    call 'CBL_OPEN_FILE' using file-path access-mode lock-mode
        device-mode stream-handle returning io-result
    if io-result not = 0 move 3 to status-code goback end-if
    move 1 to stream-opened
    call 'CBL_READ_FILE' using stream-handle stream-offset
        stream-nbytes flags-byte stream-buffer returning io-result
    if io-result not = 0
        move 3 to status-code
    else
        move stream-offset to stream-size
        move 0 to stream-offset
    end-if
    goback.
end program stream-open.

identification division.
program-id. stream-next.
data division.
local-storage section.
01 flags-byte pic x value x'00'.
01 io-result binary-long signed.
01 run-size binary-long unsigned.
01 remaining-size binary-long unsigned.
linkage section.
copy 'stream.cpy'.
01 line-data pic x any length.
01 line-size binary-long unsigned.
01 status-code binary-long signed.
procedure division using stream-state line-data line-size status-code.
    move 0 to line-size
    if status-code not = 0 goback end-if
    perform until status-code not = 0
        if stream-pos > stream-available or stream-pos = 0
            if stream-offset >= stream-size
                if line-size = 0 move 1 to stream-eof end-if
                goback
            end-if
            compute stream-nbytes = function min(65536,
                stream-size - stream-offset)
            *> Padding with NUL makes a concurrent short read invalid JSON.
            move all low-values to stream-buffer
            call 'CBL_READ_FILE' using stream-handle stream-offset
                stream-nbytes flags-byte stream-buffer
                returning io-result
            if io-result not = 0 move 3 to status-code goback end-if
            add stream-nbytes to stream-offset
            move stream-nbytes to stream-available
            move 1 to stream-pos
        end-if
        compute remaining-size = stream-available - stream-pos + 1
        move 0 to run-size
        inspect stream-buffer(stream-pos:remaining-size)
            tallying run-size for characters before initial x'0a'
        if line-size + run-size > 4000000
            move 2 to status-code goback
        end-if
        if run-size > 0
            move stream-buffer(stream-pos:run-size) to
                line-data(line-size + 1:run-size)
            add run-size to line-size stream-pos
        end-if
        if stream-pos <= stream-available
            add 1 to stream-pos
            goback
        end-if
    end-perform
    goback.
end program stream-next.

identification division.
program-id. stream-close.
data division.
local-storage section.
01 io-result binary-long signed.
linkage section.
copy 'stream.cpy'.
01 status-code binary-long signed.
procedure division using stream-state status-code.
    if stream-opened = 1
        call 'CBL_CLOSE_FILE' using stream-handle returning io-result
        if io-result not = 0 and status-code = 0
            move 3 to status-code
        end-if
        move 0 to stream-opened
    end-if
    goback.
end program stream-close.
