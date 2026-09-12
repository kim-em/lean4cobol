*> Arbitrary precision Nat arithmetic, little-endian base 10^9 limbs.
*> Inputs and output are canonical decimal blob handles. Registers are local
*> scratch arenas; no host arithmetic library or executable is used.
*> op: 1 add, 2 sub, 3 mul, 4 div, 5 mod, 6 gcd, 7 beq, 8 ble,
*>     9 land, 10 lor, 11 xor, 12 shiftLeft, 13 shiftRight, 14 pow,
*>     15 log2. A result exceeding one million limbs, or twenty million
*> limb operations, declines. Pow's kernel eligibility guard is in reduce-nat.
identification division.
program-id. bignum-calc.
data division.
local-storage section.
01 scratch-ptr usage pointer.
01 scratch-cap binary-long unsigned.
01 scratch-size binary-long unsigned.
01 limb-cap binary-long unsigned.
01 width binary-long unsigned value 32.
01 output-ptr usage pointer.
01 output-cap binary-long unsigned.
01 byte-width binary-long unsigned value 1.
01 sizes.
   02 limb-count binary-long unsigned occurs 8.
01 xreg binary-long unsigned.
01 yreg binary-long unsigned.
01 zreg binary-long unsigned.
01 i binary-long unsigned.
01 j binary-long unsigned.
01 k binary-long unsigned.
01 pos-val binary-long unsigned.
01 chunk-size binary-long unsigned.
01 text-size binary-long unsigned.
01 text-start binary-long unsigned.
01 blob-id binary-long unsigned.
01 r binary-long unsigned.
01 high-count binary-long unsigned.
01 cmp binary-long signed.
01 borrow-val binary-long unsigned.
01 signed-val binary-double signed.
01 wide-val binary-double unsigned.
01 carry-val binary-double unsigned.
01 small-val binary-long unsigned.
01 remaining-val binary-double unsigned.
01 exponent-val binary-double unsigned.
01 estimate binary-double unsigned.
01 low-val binary-double unsigned.
01 high-val binary-double unsigned.
01 middle-val binary-double unsigned.
01 qdigit binary-long unsigned.
01 digit-a binary-long unsigned.
01 digit-b binary-long unsigned.
01 bit-a binary-long unsigned.
01 bit-b binary-long unsigned.
01 bit-weight binary-long unsigned.
01 combined-val binary-long unsigned.
01 binary-count binary-long unsigned.
01 printed-limb pic 9(9).
01 first-limb pic Z(8)9.
01 work-left binary-long unsigned value 20000000.
linkage section.
copy 'state.cpy'.
copy 'blob.cpy'.
01 string-bytes based.
   02 string-byte pic x occurs 1 to 2000000000 depending on byte-cap.
01 scratch-data based.
   02 limb-row occurs 1 to 1000000 depending on limb-cap.
      03 limb binary-long unsigned occurs 8.
01 output-data based.
   02 output-byte pic x occurs 1 to 2000000000 depending on output-cap.
01 operation binary-long unsigned.
01 lhs binary-long unsigned.
01 rhs binary-long unsigned.
01 result-blob binary-long unsigned.
procedure division using kernel-state operation lhs rhs result-blob.
    move 0 to result-blob
    if verdict not = 0 goback end-if
    set address of blob-arena to blob-ptr
    compute limb-cap = function max(blob-length(lhs), blob-length(rhs)) / 9 + 3
    *> Products and binary conversion need extra headroom. Powers/shifts
    *> reserve by a conservative decimal-limb bound before doing any work.
    if operation = 3 compute limb-cap = limb-cap * 2 end-if
    if operation = 12 or 13 or 14
        set address of string-bytes to byte-ptr
        move blob-start(rhs) to text-start move blob-length(rhs) to text-size
        if text-size > 9
            move 1000000000 to exponent-val
        else
            compute exponent-val = function numval(string-bytes(text-start:text-size))
        end-if
        if operation = 12 or 14
            move blob-start(lhs) to text-start move blob-length(lhs) to text-size
            if text-size = 1 and (string-byte(text-start) = '0' or
                (operation = 14 and string-byte(text-start) = '1'))
                continue
            else
                if operation = 12
                    compute estimate = limb-cap + exponent-val / 29 + 2
                else
                    compute estimate = limb-cap * exponent-val + 2
                end-if
                if estimate > 1000000 move 2 to verdict goback end-if
                compute limb-cap = function max(limb-cap, estimate)
            end-if
        end-if
    end-if
    if limb-cap > 1000000 move 2 to verdict goback end-if
    call 'arena-reserve' using scratch-ptr scratch-cap limb-cap width verdict
    if verdict not = 0 goback end-if
    set address of scratch-data to scratch-ptr
    perform varying r from 1 by 1 until r > 2
        if r = 1 move lhs to blob-id else move rhs to blob-id end-if
        set address of blob-arena to blob-ptr
        move blob-length(blob-id) to pos-val
        move blob-start(blob-id) to text-start
        set address of string-bytes to byte-ptr
        perform until pos-val = 0
            compute chunk-size = function min(9, pos-val)
            compute i = text-start + pos-val - chunk-size
            add 1 to limb-count(r)
            compute limb(limb-count(r), r) = function numval(string-bytes(i:chunk-size))
            subtract chunk-size from pos-val
        end-perform
        perform trim-register
    end-perform
    move 1 to xreg move 2 to yreg move 3 to zreg
    evaluate operation
      when 1 perform add-registers
      when 2 perform subtract-registers
      when 3 perform multiply-registers
      when 4 when 5
        perform divide-registers
        if operation = 5 move 5 to xreg perform copy-register end-if
      when 6
        perform until limb-count(2) = 0 or verdict not = 0
            perform divide-registers
            move 2 to xreg move 1 to zreg perform copy-register
            move 5 to xreg move 2 to zreg perform copy-register
            move 1 to xreg move 2 to yreg move 3 to zreg
        end-perform
        perform copy-register
      when 7 when 8
        perform compare-registers
        if (operation = 7 and cmp = 0) or (operation = 8 and cmp <= 0)
            move 1 to limb-count(3) limb(1, 3)
        end-if
      when 9 when 10 when 11 perform bitwise-registers
      when 12 when 13 perform shift-register
      when 14 perform power-register
      when 15 perform log-register
      when other move 3 to verdict
    end-evaluate
    if verdict = 0 perform export-register end-if
    call 'arena-release' using scratch-ptr
    if output-ptr not = null call 'arena-release' using output-ptr end-if
    goback.
trim-register.
    perform until limb-count(r) = 0
        if limb(limb-count(r), r) not = 0 exit perform end-if
        subtract 1 from limb-count(r)
    end-perform.
charge-work.
    if high-count > work-left move 2 to verdict
    else subtract high-count from work-left end-if.
copy-register.
    if verdict not = 0 exit paragraph end-if
    move limb-count(xreg) to high-count perform charge-work
    if verdict not = 0 exit paragraph end-if
    move limb-count(xreg) to limb-count(zreg)
    perform varying i from 1 by 1 until i > limb-count(xreg)
        move limb(i, xreg) to limb(i, zreg)
    end-perform.
compare-registers.
    if verdict not = 0 exit paragraph end-if
    if limb-count(xreg) = limb-count(yreg)
        move limb-count(xreg) to high-count perform charge-work
        if verdict not = 0 exit paragraph end-if
    end-if
    move 0 to cmp
    evaluate true
      when limb-count(xreg) < limb-count(yreg) move -1 to cmp
      when limb-count(xreg) > limb-count(yreg) move 1 to cmp
      when other
        move limb-count(xreg) to i
        perform until i = 0
            if limb(i, xreg) < limb(i, yreg) move -1 to cmp exit perform end-if
            if limb(i, xreg) > limb(i, yreg) move 1 to cmp exit perform end-if
            subtract 1 from i
        end-perform
    end-evaluate.
add-registers.
    if verdict not = 0 exit paragraph end-if
    compute high-count = function max(limb-count(xreg), limb-count(yreg))
    perform charge-work if verdict not = 0 exit paragraph end-if
    move 0 to carry-val
    perform varying i from 1 by 1 until i > high-count
        move carry-val to wide-val
        if i <= limb-count(xreg) add limb(i, xreg) to wide-val end-if
        if i <= limb-count(yreg) add limb(i, yreg) to wide-val end-if
        divide wide-val by 1000000000 giving carry-val remainder limb(i, zreg)
    end-perform
    move high-count to limb-count(zreg)
    if carry-val not = 0
        add 1 to limb-count(zreg) move carry-val to limb(limb-count(zreg), zreg)
    end-if.
subtract-registers.
    if verdict not = 0 exit paragraph end-if
    perform compare-registers
    move 0 to limb-count(zreg)
    if cmp <= 0 exit paragraph end-if
    move limb-count(xreg) to high-count
    perform charge-work if verdict not = 0 exit paragraph end-if
    move 0 to borrow-val
    perform varying i from 1 by 1 until i > high-count
        compute signed-val = limb(i, xreg) - borrow-val
        if i <= limb-count(yreg) subtract limb(i, yreg) from signed-val end-if
        move 0 to borrow-val
        if signed-val < 0 add 1000000000 to signed-val move 1 to borrow-val end-if
        move signed-val to limb(i, zreg)
    end-perform
    move high-count to limb-count(zreg) move zreg to r perform trim-register.
multiply-registers.
    if verdict not = 0 exit paragraph end-if
    move 0 to limb-count(zreg)
    if limb-count(xreg) = 0 or limb-count(yreg) = 0 exit paragraph end-if
    compute estimate = limb-count(xreg) * limb-count(yreg)
    if estimate > work-left move 2 to verdict exit paragraph end-if
    subtract estimate from work-left
    compute high-count = limb-count(xreg) + limb-count(yreg)
    if high-count > limb-cap move 2 to verdict exit paragraph end-if
    perform varying i from 1 by 1 until i > high-count move 0 to limb(i, zreg) end-perform
    perform varying i from 1 by 1 until i > limb-count(xreg)
        move 0 to carry-val
        perform varying j from 1 by 1 until j > limb-count(yreg)
            compute k = i + j - 1
            compute wide-val = limb(i, xreg) * limb(j, yreg) + limb(k, zreg) + carry-val
            divide wide-val by 1000000000 giving carry-val remainder limb(k, zreg)
        end-perform
        compute k = i + limb-count(yreg) move carry-val to limb(k, zreg)
    end-perform
    move high-count to limb-count(zreg) move zreg to r perform trim-register.
*> In-place multiplication/division by a single limb, used for base conversion.
multiply-small.
    if verdict not = 0 exit paragraph end-if
    move limb-count(r) to high-count perform charge-work
    if verdict not = 0 exit paragraph end-if
    move 0 to carry-val
    perform varying i from 1 by 1 until i > limb-count(r)
        compute wide-val = limb(i, r) * small-val + carry-val
        divide wide-val by 1000000000 giving carry-val remainder limb(i, r)
    end-perform
    perform until carry-val = 0
        if limb-count(r) >= limb-cap move 2 to verdict exit paragraph end-if
        add 1 to limb-count(r)
        move carry-val to wide-val
        divide wide-val by 1000000000 giving carry-val remainder limb(limb-count(r), r)
    end-perform
    perform trim-register.
divide-small.
    if verdict not = 0 exit paragraph end-if
    move limb-count(r) to high-count perform charge-work
    if verdict not = 0 exit paragraph end-if
    move 0 to carry-val move limb-count(r) to i
    perform until i = 0
        compute wide-val = carry-val * 1000000000 + limb(i, r)
        divide wide-val by small-val giving limb(i, r) remainder carry-val
        subtract 1 from i
    end-perform
    perform trim-register.
*> Long division: quotient register 3, remainder 5, digit product 4.
*> Binary search on each base-10^9 quotient digit is exact even with an
*> unnormalized divisor. Single-limb divisors take one linear pass.
divide-registers.
    if verdict not = 0 exit paragraph end-if
    move 0 to limb-count(3) limb-count(5)
    if limb-count(2) = 0
        move 1 to xreg move 5 to zreg perform copy-register
        move 1 to xreg move 2 to yreg move 3 to zreg
        exit paragraph
    end-if
    if limb-count(2) = 1
        move 1 to xreg move 3 to zreg perform copy-register
        move 3 to r move limb(1, 2) to small-val perform divide-small
        if carry-val not = 0 move 1 to limb-count(5) move carry-val to limb(1, 5) end-if
        exit paragraph
    end-if
    move limb-count(1) to pos-val limb-count(3)
    perform until pos-val = 0 or verdict not = 0
        move limb-count(5) to high-count perform charge-work
        if verdict not = 0 exit perform end-if
        move limb-count(5) to i
        perform until i = 0
            compute j = i + 1 move limb(i, 5) to limb(j, 5) subtract 1 from i
        end-perform
        add 1 to limb-count(5) move limb(pos-val, 1) to limb(1, 5)
        move 5 to r perform trim-register
        move 5 to xreg move 2 to yreg perform compare-registers
        move 0 to low-val move 1 to high-val
        if cmp >= 0 move 1000000000 to high-val end-if
        perform until high-val - low-val <= 1 or verdict not = 0
            compute middle-val = (low-val + high-val) / 2
            move 2 to xreg move 4 to zreg perform copy-register
            move middle-val to small-val move 4 to r perform multiply-small
            move 4 to xreg move 5 to yreg perform compare-registers
            if cmp <= 0 move middle-val to low-val else move middle-val to high-val end-if
        end-perform
        move low-val to limb(pos-val, 3)
        if low-val not = 0 and verdict = 0
            move 2 to xreg move 4 to zreg perform copy-register
            move low-val to small-val move 4 to r perform multiply-small
            *> Subtract in place; register 5 is at least the digit product.
            move limb-count(5) to high-count perform charge-work
            if verdict not = 0 exit perform end-if
            move 0 to borrow-val
            perform varying i from 1 by 1 until i > limb-count(5)
                compute signed-val = limb(i, 5) - borrow-val
                if i <= limb-count(4) subtract limb(i, 4) from signed-val end-if
                move 0 to borrow-val
                if signed-val < 0 add 1000000000 to signed-val move 1 to borrow-val end-if
                move signed-val to limb(i, 5)
            end-perform
            move 5 to r perform trim-register
        end-if
        subtract 1 from pos-val
    end-perform
    move 3 to r perform trim-register
    move 1 to xreg move 2 to yreg move 3 to zreg.
bitwise-registers.
    move 0 to binary-count
    perform until (limb-count(1) = 0 and limb-count(2) = 0) or verdict not = 0
        move 1073741824 to small-val
        move 1 to r perform divide-small move carry-val to digit-a
        move 2 to r perform divide-small move carry-val to digit-b
        move 1 to bit-weight move 0 to combined-val
        perform 30 times
            divide digit-a by 2 giving digit-a remainder bit-a
            divide digit-b by 2 giving digit-b remainder bit-b
            if (operation = 9 and bit-a = 1 and bit-b = 1) or
               (operation = 10 and (bit-a = 1 or bit-b = 1)) or
               (operation = 11 and bit-a not = bit-b)
                add bit-weight to combined-val
            end-if
            multiply 2 by bit-weight
        end-perform
        add 1 to binary-count move combined-val to limb(binary-count, 7)
    end-perform
    perform until binary-count = 0 or verdict not = 0
        move 3 to r move 1073741824 to small-val perform multiply-small
        move limb(binary-count, 7) to carry-val move 1 to i
        perform until carry-val = 0
            if i > limb-count(3) move 0 to limb(i, 3) move i to limb-count(3) end-if
            compute wide-val = limb(i, 3) + carry-val
            divide wide-val by 1000000000 giving carry-val remainder limb(i, 3)
            add 1 to i
        end-perform
        subtract 1 from binary-count
    end-perform.
shift-register.
    move 1 to xreg move 3 to zreg perform copy-register
    if limb-count(3) = 0 exit paragraph end-if
    move exponent-val to remaining-val
    if operation = 13 and remaining-val >= limb-count(3) * 30
        move 0 to limb-count(3) exit paragraph
    end-if
    perform until remaining-val = 0 or verdict not = 0
        compute chunk-size = function min(29, remaining-val)
        compute small-val = 2 ** chunk-size
        move 3 to r
        if operation = 12 perform multiply-small else perform divide-small end-if
        subtract chunk-size from remaining-val
    end-perform.
power-register.
    move 1 to limb-count(2) limb(1, 2)
    move exponent-val to remaining-val
    perform until remaining-val = 0 or verdict not = 0
        divide remaining-val by 2 giving remaining-val remainder bit-a
        if bit-a = 1
            move 1 to xreg move 2 to yreg move 3 to zreg perform multiply-registers
            move 3 to xreg move 2 to zreg perform copy-register
        end-if
        if remaining-val not = 0
            move 1 to xreg yreg move 3 to zreg perform multiply-registers
            move 3 to xreg move 1 to zreg perform copy-register
        end-if
    end-perform
    move 2 to xreg move 3 to zreg perform copy-register.
log-register.
    move 0 to remaining-val
    perform until limb-count(1) = 0 or verdict not = 0
        move 1 to r move 1073741824 to small-val perform divide-small
        if limb-count(1) = 0
            move carry-val to digit-a
            perform until digit-a <= 1
                divide 2 into digit-a add 1 to remaining-val
            end-perform
        else add 30 to remaining-val end-if
    end-perform
    if remaining-val not = 0 move 1 to limb-count(3) move remaining-val to limb(1, 3) end-if.
export-register.
    if limb-count(3) = 0
        move 1 to text-size call 'blob-intern' using kernel-state '0' text-size result-blob
        exit paragraph
    end-if
    compute text-size = limb-count(3) * 9
    call 'arena-reserve' using output-ptr output-cap text-size byte-width verdict
    if verdict not = 0 exit paragraph end-if
    set address of output-data to output-ptr
    move limb(limb-count(3), 3) to first-limb
    compute text-size = function length(function trim(first-limb))
    move function trim(first-limb) to output-data(1:text-size)
    compute j = limb-count(3) - 1
    perform until j = 0
        move limb(j, 3) to printed-limb
        move text-size to pos-val
        add 1 to pos-val
        move printed-limb to output-data(pos-val:9)
        add 9 to text-size subtract 1 from j
    end-perform
    call 'blob-intern' using kernel-state output-data(1:text-size) text-size result-blob.
end program bignum-calc.
