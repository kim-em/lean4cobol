*> A scanner for lean4export's NDJSON. Token subtrees occupy contiguous
*> ranges; json-next skips a whole subtree. Strings are decoded once.
identification division.
program-id. json-parse.
data division.
local-storage section.
01 root-id binary-long unsigned.
01 depth-val binary-long unsigned.
linkage section.
copy 'json.cpy'.
procedure division using json-state.
    move 0 to json-count json-used scan-status
    move 1 to json-pos
    call 'json-value' using json-state root-id depth-val
    if scan-status not = 0 goback end-if
    perform until json-pos > json-length
        if json-input(json-pos:1) not = space and x'09' and x'0d'
            move 1 to scan-status exit perform
        end-if
        add 1 to json-pos
    end-perform
    goback.
end program json-parse.

identification division.
program-id. json-value recursive.
data division.
local-storage section.
01 scan-char pic x.
01 closer pic x.
01 child-id binary-long unsigned.
01 next-depth binary-long unsigned.
01 width binary-long unsigned.
01 wanted binary-long unsigned.
01 start-pos binary-long unsigned.
01 code-point binary-long unsigned.
01 high-surrogate binary-long unsigned.
01 digit-val binary-long signed.
01 i binary-long unsigned.
01 utf-left binary-long unsigned.
01 utf-min binary-long unsigned.
01 raw-byte binary-long unsigned.
linkage section.
copy 'json.cpy'.
01 result-id binary-long unsigned.
01 depth-val binary-long unsigned.
procedure division using json-state result-id depth-val.
    if scan-status not = 0 goback end-if
    if depth-val > 512 move 2 to scan-status goback end-if
    move depth-val to next-depth
    add 1 to next-depth
    perform whitespace
    if json-pos > json-length move 1 to scan-status goback end-if
    move json-count to wanted
    add 1 to wanted
    move length of json-token to width
    call 'arena-reserve' using json-ptr json-cap wanted width
        scan-status
    if scan-status not = 0 goback end-if
    set address of json-arena to json-ptr
    add 1 to json-count
    move json-count to result-id
    move json-input(json-pos:1) to scan-char
    evaluate scan-char
      when '{' when '['
        if scan-char = '{'
            move 'O' to json-kind(result-id) move '}' to closer
        else
            move 'A' to json-kind(result-id) move ']' to closer
        end-if
        add 1 to json-pos
        perform whitespace
        if json-pos <= json-length and
            json-input(json-pos:1) = closer
            add 1 to json-pos
        else
            perform children
        end-if
      when '"'
        move 'S' to json-kind(result-id)
        compute json-start(result-id) = json-used + 1
        perform string-value
        compute json-size(result-id) =
            json-used + 1 - json-start(result-id)
      when 't'
        move 'T' to json-kind(result-id)
        if json-pos + 3 <= json-length and
            json-input(json-pos:4) = 'true'
            add 4 to json-pos
        else move 1 to scan-status end-if
      when 'f'
        move 'F' to json-kind(result-id)
        if json-pos + 4 <= json-length and
            json-input(json-pos:5) = 'false'
            add 5 to json-pos
        else move 1 to scan-status end-if
      when 'n'
        move 'Z' to json-kind(result-id)
        if json-pos + 3 <= json-length and
            json-input(json-pos:4) = 'null'
            add 4 to json-pos
        else move 1 to scan-status end-if
      when other
        move 'N' to json-kind(result-id)
        move json-pos to start-pos
        perform number-value
        compute json-start(result-id) = json-used + 1
        compute json-size(result-id) = json-pos - start-pos
        if scan-status = 0
            move json-input(start-pos:json-size(result-id)) to
                json-decoded(json-used + 1:json-size(result-id))
            add json-size(result-id) to json-used
        end-if
    end-evaluate
    set address of json-arena to json-ptr
    compute json-next(result-id) = json-count + 1
    goback.
whitespace.
    perform until json-pos > json-length
        if json-input(json-pos:1) not = space and x'09' and x'0d'
            exit perform
        end-if
        add 1 to json-pos
    end-perform.
children.
    perform until scan-status not = 0
        if closer = '}'
            if json-pos > json-length or
                json-input(json-pos:1) not = '"'
                move 1 to scan-status exit paragraph
            end-if
            call 'json-value' using json-state child-id next-depth
            if scan-status not = 0 exit paragraph end-if
            perform whitespace
            if json-pos > json-length or
                json-input(json-pos:1) not = ':'
                move 1 to scan-status exit paragraph
            end-if
            add 1 to json-pos
        end-if
        call 'json-value' using json-state child-id next-depth
            if scan-status not = 0 exit paragraph end-if
        perform whitespace
        if json-pos > json-length
            move 1 to scan-status exit paragraph
        end-if
        move json-input(json-pos:1) to scan-char
        add 1 to json-pos
        if scan-char = closer exit paragraph end-if
        if scan-char not = ',' move 1 to scan-status exit paragraph end-if
        perform whitespace
    end-perform.
number-value.
    if json-input(json-pos:1) = '-' add 1 to json-pos end-if
    if json-pos > json-length
        move 1 to scan-status exit paragraph
    end-if
    if json-input(json-pos:1) = '0'
        add 1 to json-pos
    else
        if json-input(json-pos:1) < '1' or > '9'
            move 1 to scan-status exit paragraph
        end-if
        perform digits
    end-if
    if json-pos <= json-length and json-input(json-pos:1) = '.'
        add 1 to json-pos
        perform required-digits
    end-if
    if json-pos <= json-length and
        (json-input(json-pos:1) = 'e' or 'E')
        add 1 to json-pos
        if json-pos <= json-length and
            (json-input(json-pos:1) = '+' or '-')
            add 1 to json-pos
        end-if
        perform required-digits
    end-if.
required-digits.
    if json-pos > json-length or
        json-input(json-pos:1) < '0' or > '9'
        move 1 to scan-status
    else perform digits end-if.
digits.
    perform until json-pos > json-length
        if json-input(json-pos:1) < '0' or > '9' exit perform end-if
        add 1 to json-pos
    end-perform.
string-value.
    add 1 to json-pos
    perform until json-pos > json-length or scan-status not = 0
        move json-input(json-pos:1) to scan-char
        add 1 to json-pos
        if scan-char = '"'
            if utf-left not = 0 move 1 to scan-status end-if
            exit paragraph
        end-if
        compute raw-byte = function ord(scan-char) - 1
        if raw-byte < 32 move 1 to scan-status exit paragraph end-if
        if scan-char = x'5c'
            if utf-left not = 0 or json-pos > json-length
                move 1 to scan-status exit paragraph
            end-if
            move json-input(json-pos:1) to scan-char
            add 1 to json-pos
            evaluate scan-char
              when '"' when x'5c' when '/' continue
              when 'b' move x'08' to scan-char
              when 'f' move x'0c' to scan-char
              when 'n' move x'0a' to scan-char
              when 'r' move x'0d' to scan-char
              when 't' move x'09' to scan-char
              when 'u'
                perform hex-four
                if code-point >= 55296 and <= 56319
                    move code-point to high-surrogate
                    if json-pos + 1 > json-length or
                        json-input(json-pos:2) not = x'5c75'
                        move 1 to scan-status exit paragraph
                    end-if
                    add 2 to json-pos
                    perform hex-four
                    if code-point < 56320 or > 57343
                        move 1 to scan-status exit paragraph
                    end-if
                    compute code-point = 65536 +
                        (high-surrogate - 55296) * 1024 +
                        code-point - 56320
                else
                    if code-point >= 56320 and <= 57343
                        move 1 to scan-status exit paragraph
                    end-if
                end-if
                if scan-status not = 0 exit paragraph end-if
                perform encode-utf8
              when other move 1 to scan-status exit paragraph
            end-evaluate
            if scan-char not = 'u' perform append-byte end-if
        else
            perform validate-utf8
            perform append-byte
        end-if
    end-perform
    move 1 to scan-status.
append-byte.
    add 1 to json-used
    move scan-char to json-decoded(json-used:1).
hex-four.
    move 0 to code-point
    perform 4 times
        if json-pos > json-length
            move 1 to scan-status exit paragraph
        end-if
        compute digit-val = function ord(
            function lower-case(json-input(json-pos:1)))
        evaluate true
          when digit-val >= 49 and <= 58 subtract 49 from digit-val
          when digit-val >= 98 and <= 103 subtract 88 from digit-val
          when other move 1 to scan-status exit paragraph
        end-evaluate
        compute code-point = code-point * 16 + digit-val
        add 1 to json-pos
    end-perform.
encode-utf8.
    evaluate true
      when code-point < 128
        move function char(code-point + 1) to scan-char
        perform append-byte
      when code-point < 2048
        move function char(193 + function integer(code-point / 64))
            to scan-char
        perform append-byte
        perform emit-last-byte
      when code-point < 65536
        move function char(225 +
            function integer(code-point / 4096)) to scan-char
        perform append-byte
        perform emit-middle-byte
        perform emit-last-byte
      when other
        move function char(241 +
            function integer(code-point / 262144)) to scan-char
        perform append-byte
        move function char(129 + function mod(
            function integer(code-point / 4096), 64)) to scan-char
        perform append-byte
        perform emit-middle-byte
        perform emit-last-byte
    end-evaluate
    move 'u' to scan-char.
emit-middle-byte.
    move function char(129 + function mod(
        function integer(code-point / 64), 64)) to scan-char
    perform append-byte.
emit-last-byte.
    move function char(129 + function mod(code-point, 64)) to scan-char
    perform append-byte.
validate-utf8.
    if utf-left = 0
        evaluate true
          when raw-byte < 128 continue
          when raw-byte >= 194 and <= 223
            move 1 to utf-left move 128 to utf-min
            move raw-byte to code-point
            subtract 192 from code-point
          when raw-byte >= 224 and <= 239
            move 2 to utf-left move 2048 to utf-min
            move raw-byte to code-point
            subtract 224 from code-point
          when raw-byte >= 240 and <= 244
            move 3 to utf-left move 65536 to utf-min
            move raw-byte to code-point
            subtract 240 from code-point
          when other move 1 to scan-status
        end-evaluate
    else
        if raw-byte < 128 or > 191
            move 1 to scan-status exit paragraph
        end-if
        compute code-point = code-point * 64 + raw-byte - 128
        subtract 1 from utf-left
        if utf-left = 0 and (code-point < utf-min or
            code-point > 1114111 or
            (code-point >= 55296 and <= 57343))
            move 1 to scan-status
        end-if
    end-if.
end program json-value.

identification division.
program-id. json-field.
data division.
local-storage section.
01 i binary-long unsigned.
01 v binary-long unsigned.
linkage section.
copy 'json.cpy'.
01 parent-id binary-long unsigned.
01 field-name pic x any length.
01 result-id binary-long unsigned.
procedure division using json-state parent-id field-name result-id.
    move 0 to result-id
    if scan-status not = 0 goback end-if
    set address of json-arena to json-ptr
    if parent-id = 0 or parent-id > json-count
        move 1 to scan-status goback
    end-if
    if json-kind(parent-id) not = 'O'
        move 1 to scan-status goback
    end-if
    move parent-id to i
    add 1 to i
    perform until i >= json-next(parent-id)
        move i to v
        add 1 to v
        if json-size(i) = function length(field-name) and
            json-decoded(json-start(i):json-size(i)) = field-name
            if result-id not = 0
                move 1 to scan-status goback
            end-if
            move v to result-id
        end-if
        move json-next(v) to i
    end-perform
    goback.
end program json-field.

identification division.
program-id. json-natural.
data division.
local-storage section.
01 i binary-long unsigned.
01 digit-val binary-long unsigned.
linkage section.
copy 'json.cpy'.
01 token-id binary-long unsigned.
01 result-val binary-double unsigned.
procedure division using json-state token-id result-val.
    move 0 to result-val
    if scan-status not = 0 goback end-if
    set address of json-arena to json-ptr
    if token-id = 0 or token-id > json-count
        move 1 to scan-status goback
    end-if
    if json-kind(token-id) not = 'N'
        move 1 to scan-status goback
    end-if
    perform varying i from json-start(token-id) by 1
        until i >= json-start(token-id) + json-size(token-id)
        if json-decoded(i:1) < '0' or > '9'
            move 1 to scan-status goback
        end-if
        compute digit-val = function ord(json-decoded(i:1)) - 49
        if result-val > 1844674407370955161 or
            (result-val = 1844674407370955161 and digit-val > 5)
            move 2 to scan-status goback
        end-if
        compute result-val = result-val * 10 + digit-val
    end-perform
    goback.
end program json-natural.
