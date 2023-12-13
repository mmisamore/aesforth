#! /usr/bin/gforth

\ AES implementation for 256-bit keys in Gforth by Michael Misamore.
\ Changelog: 
\ 17 Feb 2009 First release; unoptimized.
\ 6  Apr 2009 Mildly optimized: precomputed lookup tables for some products.
\             Faster substitution. Dynamically generates sbox, isbox.
\ 12 Apr 2009 Use /mod for faster address arithmetic. Faster substitution.
\ This software is distributed under the terms of the GNU General Public
\ License, version 3.0 (see LICENSE). This code is only intended as a
\ reference. Targeted for platforms with 32-bit words (but safe for 64-bit
\ platforms as well).

variable stateArray 4 cells allot      \ 4 32-bit words of state
variable w 15 4 * cells allot          \ (Nr + 1)*4 (4 32-bit words per round)
variable sbox 256 4 / cells allot      \ 256 byte sbox
variable isbox 256 4 / cells allot     \ 256 byte inverse sbox
variable ckey 8 cells allot            \ 256 bit secret key
variable rcon 7 cells allot            \ rcon array, per spec
variable 09timeTab 256 4 / cells allot \ {09} times table
variable 0btimeTab 256 4 / cells allot \ {0b} times table
variable 0dtimeTab 256 4 / cells allot \ {0d} times table
variable 0etimeTab 256 4 / cells allot \ {0e} times table
variable logTab 256 4 / cells allot    \ log lookup table
variable expTab 256 4 / cells allot    \ exp lookup table

\ Show state array for debugging ( -- )
: showStateArray cr 4 0 do i cells stateArray + @ hex. cr loop ;

\ Get ith array byte entry ( n1 n2 -- n ) n1 = array, n2 = byte#
: getByteEntry 4 /mod cells + + c@ ;

\ Combine four bytes into a 32-bit word ( n1 n2 n3 n4 -- n )
: 4BytesToWord 8 lshift + 8 lshift + 8 lshift + ;

\ Show the sboxes for debugging ( -- )
: showSbox cr 256 0 do i dup sbox swap getByteEntry hex. 16 mod 15 =
    if cr then loop ;

\ Put ith array byte entry ( n1 n2 n3 -- ) n1 = array, n2 = byte#, n3 = byte
: putByteEntry -rot 4 /mod cells + + c! ;

\ Substitute a 32-bit word ( n1 n2 -- n ) n1 = substitution array, n2 = word
: subWord 4 0 do over over $ff and getByteEntry -rot 8 rshift loop 2drop
    4BytesToWord ;

\ Basic multiplication in GF(2^8) ( n -- n )
: xtime dup 2* swap $80 and if $11b xor then ; \ Mult by x = {02} = 0010
: xtimes+ dup xtime xor ;                      \ Mult by x+1 = {03} = 0011

\ Build exp, log tables, define exp, log to base x+1 in GF(2^8)
: buildExpTab expTab $1 over ! $3 over 1+ ! drop $3 256 2
    do xtimes+ dup i swap expTab -rot putByteEntry loop drop ; buildExpTab
: expx expTab swap getByteEntry ; ( n -- n ) \ Fast exp
: lx 256 0 do i tuck expx over = if drop leave then swap drop loop ; ( n -- n)
: buildLogTab 256 0 do logTab i dup lx putByteEntry loop ; buildLogTab
: logx logTab swap getByteEntry ; ( n -- n ) \ Fast log

\ Multiply two elements in GF(2^8) ( n1 n2 -- n )
: gf8m logx swap logx + 255 mod expx ; \ nonzero case
: gf8mult 2dup * 0= if 2drop 0 exit then gf8m ;

\ Precompute some of the harder products; store in tables
: build09Tab 256 0 do 09timeTab i dup $9 gf8mult putByteEntry loop ; build09Tab
: build0bTab 256 0 do 0btimeTab i dup $b gf8mult putByteEntry loop ; build0bTab
: build0dTab 256 0 do 0dtimeTab i dup $d gf8mult putByteEntry loop ; build0dTab
: build0eTab 256 0 do 0etimeTab i dup $e gf8mult putByteEntry loop ; build0eTab

\ Multiply in GF(2^8) ( n -- n )
: 09time 09timeTab swap getByteEntry ; \ Mult by {09} = 1001
: 0btime 0btimeTab swap getByteEntry ; \ Mult by {0b} = 1011
: 0dtime 0dtimeTab swap getByteEntry ; \ Mult by {0d} = 1101
: 0etime 0etimeTab swap getByteEntry ; \ Mult by {0e} = 1110

\ Compute the multiplicative inverse in GF(2^8) ( n -- n )
: invgf8 dup 0<> if logx 255 swap - expx then ;

\ Dynamically compute ith sbox, isbox elements ( n -- n )
: sBoxElt invgf8 dup 4 0 do dup 1 lshift swap 7 rshift or tuck xor swap loop
    drop $63 xor $ff and ;
: r5l3 dup 5 rshift swap 3 lshift or ;  \ bit rotates
: l5r3 dup 5 lshift swap 3 rshift or ;
: r2l6 dup 2 rshift swap 6 lshift or ;
: isBoxElt $63 xor dup r5l3 over l5r3 xor xor $ff and r2l6 $ff and invgf8 ;

\ Build sbox, isbox at load time ( -- )
: buildSbox 256 0 do sbox i dup sBoxElt putByteEntry loop ; buildSbox
: buildISbox 256 0 do isbox i dup isBoxElt putByteEntry loop ; buildISBox

\ Shift functions ( n -- n )
: ishiftbyone dup 24 rshift swap 8 lshift $ffffff00 and xor ;
: ishiftbytwo dup 16 rshift swap 16 lshift $ffff0000 and xor ;
: ishiftbythree dup $ff and 24 lshift swap 8 rshift xor ;
: ishiftrows stateArray cell+ dup @ ishiftbyone over !
                       cell+ dup @ ishiftbytwo over !
                       cell+ dup @ ishiftbythree over ! drop ;
: shiftrows stateArray cell+ dup @ ishiftbythree over !
                       cell+ dup @ ishiftbytwo over !
                       cell+ dup @ ishiftbyone over ! drop ;

\ Transform the state by the given substitution array ( n1 -- )
: subBytes 4 0 do i cells stateArray + dup @ rot tuck swap subWord
    rot ! loop drop ;

\ Fetch the ith column of state ( n1 n2 -- n ) 
\ n1 = state array, n2 = col#
: fetchIthCol + dup c@ swap cell+ dup c@ swap cell+ dup c@ swap cell+
    dup c@ swap drop 4BytesToWord ;

\ Store the ith column of state ( n1 n2 n3 -- )
\ n1 = state array, n2 = col#, n3 = word to store
: storeIthCol swap rot + swap 4 0 do dup $ff and rot tuck c! cell+
    swap 8 rshift loop 2drop ;

\ Reverse byte order of a word ( n -- n )
: trans dup $ff and 24 lshift swap dup $ff00 and 8 lshift swap dup $ff0000
    and 8 rshift swap $ff000000 and 24 rshift + + + ;

\ Add a given round key to the state ( n -- ) n = address of round key
: addRoundKey 4 0 do stateArray i fetchIthCol swap dup i cells + @ rot
    xor stateArray swap i swap storeIthCol loop drop ;

\ Words for mixing columns
: bByte dup $ff and ; ( n -- n n ) \ Get bottom byte
: mixCol0 bByte xtime swap 8 rshift bByte xtimes+ rot xor swap
                           8 rshift bByte rot xor swap
                           8 rshift xor ; ( n -- n ) \ 0th new col byte
: mixCol1 bByte swap 8 rshift bByte xtime rot xor swap
                     8 rshift bByte xtimes+ swap
                     8 rshift xor xor ; \ 1st new col byte
: mixCol2 bByte swap 8 rshift bByte rot xor swap
                     8 rshift bByte xtime rot xor swap
                     8 rshift xtimes+ xor ; \ 2nd new col byte
: mixCol3 bByte xtimes+ swap 8 rshift bByte rot xor swap
                        8 rshift bByte rot xor swap
                        8 rshift xtime xor ; \ 3rd new col byte
: mixCol dup mixCol0 swap dup mixCol1 swap dup mixCol2 swap mixCol3
    4BytesToWord ; ( n -- n ) \ Mix a given column

: mixColumns 4 0 do dup i fetchIthCol over swap mixCol i swap
    storeIthCol loop drop ; ( n -- ) \ Given state array, mix it

\ Words for inverted column mixing
: imixCol0 bByte 0etime swap 8 rshift bByte 0btime rot xor swap
                             8 rshift bByte 0dtime rot xor swap
                             8 rshift 09time xor ; \ 0th new col byte
: imixCol1 bByte 09time swap 8 rshift bByte 0etime rot xor swap
                             8 rshift bByte 0btime rot xor swap
                             8 rshift 0dtime xor ; \ 1st new col byte
: imixCol2 bByte 0dtime swap 8 rshift bByte 09time rot xor swap
                             8 rshift bByte 0etime rot xor swap
                             8 rshift 0btime xor ; \ 2nd new col byte
: imixCol3 bByte 0btime swap 8 rshift bByte 0dtime rot xor swap
                             8 rshift bByte 09time rot xor swap
                             8 rshift 0etime xor ; \ 3rd new col byte
: imixCol dup imixCol0 swap dup imixCol1 swap dup imixCol2 swap imixCol3
    4BytesToWord ; ( n -- n ) \ Inverse mix column

: imixColumns 4 0 do dup i fetchIthCol over swap imixCol i swap
    storeIthCol loop drop ; ( n -- ) \ Given state array, inverse mix

\ 256 bit test key
ckey $00010203 over ! cell+ $04050607 over ! cell+ $08090a0b over ! cell+
     $0c0d0e0f over ! cell+ $10111213 over ! cell+ $14151617 over ! cell+
     $18191a1b over ! cell+ $1c1d1e1f over ! drop

\ array of powers of x
rcon $01000000 over ! cell+ $02000000 over ! cell+ $04000000 over ! cell+
     $08000000 over ! cell+ $10000000 over ! cell+ $20000000 over ! cell+
     $40000000 over ! drop

\ copy cipher key to beginning of key schedule ( -- )
: copyckey 8 0 do ckey i cells + @ w i cells + ! loop ;

\ expand the rest of the key schedule ( -- )
: expandrest 60 8 do w i 1- cells + @
   i 8 mod 0 = if  \ Nk = 8
      ishiftbyone sbox swap subWord i 8 / 1- cells rcon + @ xor
   else
      i 8 mod 4 = if
         sbox swap subWord
      then
   then i 8 - cells w + @ xor i cells w + ! loop ;

\ reverse the words in the key ( -- )
: reverseKeyWords 15 4 * 0 do i cells w + dup @ trans swap ! loop ;

copyckey expandrest reverseKeyWords \ create the key schedule for ckey

\ plaintext test: $001122334455...
stateArray $cc884400 over ! cell+ $dd995511 over ! cell+
           $eeaa6622 over ! cell+ $ffbb7733 over ! drop

: aes256-encrypt w addRoundKey 14 1 do sbox subBytes shiftrows stateArray
    mixColumns i 4 * cells w + addRoundKey loop sbox subBytes shiftrows
    14 4 * cells w + addRoundKey ; ( -- )

: aes256-decrypt 14 4 * cells w + addRoundKey 1 13 do ishiftrows isbox
    subBytes i 4 * cells w + addRoundKey stateArray imixColumns -1 +loop
    ishiftrows isbox subBytes w addRoundKey ; ( -- )
