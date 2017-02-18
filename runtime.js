///////// CORE_KERNEL
//Provides: int_math_int_pow_stub
function int_math_int_pow_stub(base, exponent){
  var one = 1;
  var mul = [one, base, one, one];
  var res = one;
  while (!exponent==0) {
    mul[1] = (mul[1] * mul[3]) | 0;
    mul[2] = (mul[1] * mul[1]) | 0;
    mul[3] = (mul[2] * mul[1]) | 0;
    res = (res * mul[exponent& 3]) | 0;
    exponent = exponent >> 2;
  }
  return res;
}

//Provides: int_math_int64_pow_stub
//Requires: caml_int64_mul, caml_int64_is_zero, caml_int64_shift_right_unsigned
function int_math_int64_pow_stub(base, exponent){
  var one = [255,1,0,0];
  var mul = [one, base, one, one];
  var res = one;
  while (!caml_int64_is_zero(exponent)) {
    mul[1] = caml_int64_mul(mul[1],mul[3]);
    mul[2] = caml_int64_mul(mul[1],mul[1]);
    mul[3] = caml_int64_mul(mul[2],mul[1]);
    res = caml_int64_mul(res, mul[exponent[1]& 3]);
    exponent = caml_int64_shift_right_unsigned(exponent, 2);
  }
  return res;
}

//Provides: int_math_int_popcount
function int_math_int_popcount(v) {
  v = v - ((v >>> 1) & 0x55555555);
  v = (v & 0x33333333) + ((v >>> 2) & 0x33333333);
  return ((v + (v >>> 4) & 0xF0F0F0F) * 0x1010101) >>> 24;
}

//Provides: caml_hash_string
//Requires: caml_hash
function caml_hash_string(s) {
  return caml_hash(1,1,0,s)
}
//Provides: caml_hash_double
//Requires: caml_hash
function caml_hash_double(d) {
  return caml_hash(1,1,0,d);
}

//Provides: core_heap_block_is_heap_block
function core_heap_block_is_heap_block(x){
  return +(x instanceof Array);
}

//Provides: core_array_unsafe_int_blit
//Requires: caml_array_blit
var core_array_unsafe_int_blit = caml_array_blit
//Provides: core_array_unsafe_float_blit
//Requires: caml_array_blit
var core_array_unsafe_float_blit = caml_array_blit

//Provides: core_kernel_time_ns_gettime_or_zero
//Requires: caml_int64_mul, caml_int64_of_float, caml_int64_of_int32
var ms_to_nano = caml_int64_of_int32(1000*1000);
function core_kernel_time_ns_gettime_or_zero(){
  var ms = Date.now();
  var ms_i64 = caml_int64_of_float(ms);
  return caml_int64_mul(ms_i64,ms_to_nano);
}
//Provides: core_kernel_time_ns_format
//Requires: caml_to_js_string, caml_js_to_string
function core_kernel_time_ns_format(time,format){
  var d = new Date(time * 1000);
  var formatjs = caml_to_js_string(format);
  var jstring = joo_global_object.strftime(formatjs, d);
  return caml_js_to_string(jstring);
}

//Provides: core_kernel_gc_compactions
function core_kernel_gc_compactions () { return 0 }
//Provides: core_kernel_gc_heap_chunks
function core_kernel_gc_heap_chunks () { return 0 }
//Provides: core_kernel_gc_heap_words
function core_kernel_gc_heap_words () { return 0 }
//Provides: core_kernel_gc_major_collections
function core_kernel_gc_major_collections () { return 0 }
//Provides: core_kernel_gc_major_plus_minor_words
function core_kernel_gc_major_plus_minor_words () { return 0 }
//Provides: core_kernel_gc_major_words
function core_kernel_gc_major_words () { return 0 }
//Provides: core_kernel_gc_minor_collections
function core_kernel_gc_minor_collections () { return 0 }
//Provides: core_kernel_gc_minor_words
function core_kernel_gc_minor_words () { return 0 }
//Provides: core_kernel_gc_promoted_words
function core_kernel_gc_promoted_words () { return 0 }
//Provides: core_kernel_gc_top_heap_words
function core_kernel_gc_top_heap_words () { return 0 }
//Provides: clear_caml_backtrace_pos
function clear_caml_backtrace_pos () { return 0 }

//Provides: internalhash_fold_int64
//Requires: caml_hash_mix_int64
var internalhash_fold_int64 = caml_hash_mix_int64
//Provides: internalhash_fold_int
//Requires: caml_hash_mix_int
var internalhash_fold_int = caml_hash_mix_int
//Provides: internalhash_fold_float
//Requires: caml_hash_mix_float
var internalhash_fold_float = caml_hash_mix_float
//Provides: internalhash_fold_string
//Requires: caml_hash_mix_string
var internalhash_fold_string = caml_hash_mix_string
//Provides: internalhash_fold_bigstring
//Requires: caml_hash_mix_bigstring
var internalhash_fold_bigstring = caml_hash_mix_bigstring
//Provides: internalhash_get_hash_value
//Requires: caml_hash_mix_final
function internalhash_get_hash_value (seed) {
  var h = caml_hash_mix_final(seed);
  return h & 0x3FFFFFFF;
}
///////// BIN_PROT

//Provides: bin_prot_get_float_offset
//Requires: caml_float_of_bytes, caml_ba_get_1
function bin_prot_get_float_offset(a,p){
  var t = new Array(8);;
  for (var i = 0;i < 8;i++) t[7-i] = caml_ba_get_1(a,p++);
  var v = caml_float_of_bytes (t);
  return [254,v];
}


//Provides: bin_prot_blit_buf_float_array_stub
//Requires: caml_array_set, caml_ba_get_1
//Requires: caml_int64_of_bytes, caml_int64_float_of_bits 
function bin_prot_blit_buf_float_array_stub(v_src_pos, v_buf, v_dst_pos, v_arr, v_len){
  var c;
  var t = new Array(8);;
  for(var i = 0; i < v_len; i++){
    for (var j = 0;j < 8;j++) t[7-j] = caml_ba_get_1(v_buf,v_src_pos+j+(i*8));
    c = caml_int64_float_of_bits (caml_int64_of_bytes (t));
    caml_array_set(v_arr,v_dst_pos+i,c);
  }
  return 0
}
//Provides: bin_prot_blit_buf_string_stub
//Requires: caml_ba_get_1, caml_string_unsafe_set
function bin_prot_blit_buf_string_stub(v_src_pos, v_buf, v_dst_pos, v_str, v_len){
  var c;
  for(var i = 0; i < v_len; i++){
    c = caml_ba_get_1(v_buf,v_src_pos+i);
    caml_string_unsafe_set(v_str,v_dst_pos+i,c);
  }
  return 0
}
//Provides: bin_prot_blit_float_array_buf_stub
//Requires: caml_array_get, caml_ba_set_1
//Requires: caml_int64_to_bytes, caml_int64_bits_of_float
function bin_prot_blit_float_array_buf_stub(v_src_pos, v_arr, v_dst_pos, v_buf, v_len){
  var c;
  for(var i = 0; i < v_len; i++){
    var f = caml_array_get(v_arr,v_src_pos+i);
    var a = caml_int64_to_bytes(caml_int64_bits_of_float(f));
    for (var j = 0;j < 8;j++)
      caml_ba_set_1(v_buf,v_dst_pos+j+(i*8), a[7-j]);
  }
  return 0
}
//Provides: bin_prot_blit_string_buf_stub
//Requires: caml_string_unsafe_get, caml_ba_set_1
function bin_prot_blit_string_buf_stub (v_src_pos, v_str, v_dst_pos, v_buf, v_len){
  var c;
  for(var i = 0; i < v_len; i++){
    c = caml_string_unsafe_get(v_str,v_src_pos+i);
    caml_ba_set_1(v_buf,v_dst_pos+i,c);
  }
  return 0
}

//Provides: bin_prot_blit_buf_stub
//Requires: caml_ba_get_1, caml_ba_set_1, bigstring_of_array_buffer
function bin_prot_blit_buf_stub (v_src_pos, v_src, v_dst_pos, v_dst, v_len){
  var v_src2 = bigstring_of_array_buffer(v_src.data.buffer);
  var v_dst2 = bigstring_of_array_buffer(v_dst.data.buffer);
  var c;
  for(var i = 0; i < v_len; i++){
    c = caml_ba_get_1(v_src2,v_src_pos+i);
    caml_ba_set_1(v_dst2,v_dst_pos+i,c);
  }
  return 0
}
// Requires that Sys.word_size == 32, which it is for js_of_ocaml
// This issue is not avoidable without rolling a custom nums.cma
"use strict";

//Provides: initialize_nat
function initialize_nat() {
	return undefined;
}

//Provides: create_nat
function create_nat(size) {
	// length_nat isn't external, so we have to make the Obj.size
	// work out right. The +2 to array length seems to work.
	var arr = [-1, -1];
	for(var i = 2; i < size+2; i++) {
		arr[i] = -1;
	}
	return arr;
}

//Provides: set_to_zero_nat
function set_to_zero_nat(nat, ofs, len) {
	for(var i = 0; i < len; i++) {
		nat[ofs+i] = 0;
	}
	return undefined;
}

//Provides: blit_nat
function blit_nat(nat1, ofs1, nat2, ofs2, len) {
	for(var i = 0; i < len; i++) {
		nat1[ofs1+i] = nat2[ofs2+i];
	}
	return undefined;
}

//Provides: set_digit_nat
function set_digit_nat(nat, ofs, digit) {
	nat[ofs] = digit;
	if(nat[ofs] < 0) nat[ofs] += 4294967296;
	return undefined;
}

//Provides: nth_digit_nat
function nth_digit_nat(nat, ofs) {
	return nat[ofs];
}

//Provides: set_digit_nat_native
function set_digit_nat_native(nat, ofs, digit) {
	nat[ofs] = digit;
	if(nat[ofs] < 0) nat[ofs] += 4294967296;
	return undefined;
}

//Provides: nth_digit_nat_native
function nth_digit_nat_native(nat, ofs) {
	return nat[ofs];
}

//Provides: num_digits_nat
function num_digits_nat(nat, ofs, len) {
	for(var i = len - 1; i >= 0; i--) {
		if(nat[ofs+i] != 0) return i+1;
	}
	return 1; // 0 counts as 1 digit
}

//Provides: num_leading_zero_bits_in_digit
function num_leading_zero_bits_in_digit(nat, ofs) {
	var a = nat[ofs];
	var b = 0;
	if(a & 0xFFFF0000) { b +=16; a >>>=16; }
	if(a & 0xFF00)     { b += 8; a >>>= 8; }
	if(a & 0xF0)       { b += 4; a >>>= 4; }
	if(a & 12)         { b += 2; a >>>= 2; }
	if(a & 2)          { b += 1; a >>>= 1; }
	if(a & 1)          { b += 1; }
	return 32 - b;
}

//Provides: is_digit_int
function is_digit_int(nat, ofs) {
	return nat[ofs] < 4294967296 / 4;
}

//Provides: is_digit_zero
function is_digit_zero(nat, ofs) {
	return nat[ofs] == 0;
}

//Provides: is_digit_odd
function is_digit_odd(nat, ofs) {
	return nat[ofs] & 1 == 1;
}

//Provides: incr_nat
function incr_nat(nat, ofs, len, carry_in) {
	var carry = carry_in;
	for(var i = 0; i < len; i++) {
		nat[ofs+i] += carry;
		if(nat[ofs+i] < 4294967296) {
			carry = 0;
			break;
		} else {
			nat[ofs+i] -= 4294967296;
			carry = 1;
		}
	}
	return carry;
}

// len1 >= len2
//Provides: add_nat
//Requires: incr_nat
function add_nat(nat1, ofs1, len1, nat2, ofs2, len2, carry_in) {
	var carry = carry_in;
	for(var i = 0; i < len2; i++) {
		nat1[ofs1+i] += nat2[ofs2+i] + carry;
		if(nat1[ofs1+i] < 4294967296) {
			carry = 0;
		} else {
			nat1[ofs1+i] -= 4294967296;
			carry = 1;
		}
	}
	return incr_nat(nat1, ofs1+len2, len1-len2, carry);
}

//Provides: complement_nat
function complement_nat(nat, ofs, len) {
	for(var i = 0; i < len; i++) {
		nat[ofs+i] = 4294967296 - 1 - nat[ofs+i];
	}
}

// ocaml flips carry_in
//Provides: decr_nat
function decr_nat(nat, ofs, len, carry_in) {
	var borrow = (carry_in == 1) ? 0 : 1;
	for(var i = 0; i < len; i++) {
		nat[ofs+i] -= borrow;
		if (nat[ofs+i] >= 0) {
			borrow = 0;
			break;
		} else {
			nat[ofs+i] += 4294967296;
			borrow = 1;
		}
	}
	return (borrow == 1) ? 0 : 1;
}

// ocaml flips carry_in
// len1 >= len2
//Provides: sub_nat
//Requires: decr_nat
function sub_nat(nat1, ofs1, len1, nat2, ofs2, len2, carry_in) {
	var borrow = (carry_in == 1) ? 0 : 1;
	for(var i = 0; i < len2; i++) {
		nat1[ofs1+i] -= nat2[ofs2+i] + borrow;
		if (nat1[ofs1+i] >= 0) {
			borrow = 0;
		} else {
			nat1[ofs1+i] += 4294967296;
			borrow = 1;
		}
	}
	return decr_nat(nat1, ofs1+len2, len1-len2, (borrow==1)?0:1);
}

// nat1 += nat2 * nat3[ofs3]
// len1 >= len2
//Provides: mult_digit_nat
//Requires: add_nat
function mult_digit_nat(nat1, ofs1, len1, nat2, ofs2, len2, nat3, ofs3) {
	var carry = 0;
	var a = nat3[ofs3];
	for(var i = 0; i < len2; i++) {
		nat1[ofs1+i] += nat2[ofs2+i] * (a & 0x0000FFFF) + carry;
		var x = nat2[ofs2+i] * (a >>> 16);
		carry = Math.floor(x/65536);
		nat1[ofs1+i] += (x % 65536) * 65536;
		carry += Math.floor(nat1[ofs1+i]/4294967296);
		nat1[ofs1+i] %= 4294967296;
	}

	if(len2 < len1 && carry) {
		return add_nat(nat1, ofs1+len2, len1-len2, [carry], 0, 1, 0);
	} else {
		return carry;
	}
}

// nat1 += nat2 * nat3
// len1 >= len2 + len3.
//Provides: mult_nat
//Requires: mult_digit_nat
function mult_nat(nat1, ofs1, len1, nat2, ofs2, len2, nat3, ofs3, len3) {
	var carry = 0;
	for(var i = 0; i < len3; i++) {
		carry += mult_digit_nat(nat1, ofs1+i, len1-i, nat2, ofs2, len2, nat3, ofs3+i);
	}
	return carry;
}

// nat1 = 2 * nat1 + nat2 * nat2
// len1 >= 2 * len2
//Provides: square_nat
//Requires: mult_nat, add_nat
function square_nat(nat1, ofs1, len1, nat2, ofs2, len2) {
	var carry = 0;
	carry += add_nat(nat1, ofs1, len1, nat1, ofs1, len1, 0);
	carry += mult_nat(nat1, ofs1, len1, nat2, ofs2, len2, nat2, ofs2, len2);
	return carry;
}


// 0 <= shift < 32
//Provides: shift_left_nat
function shift_left_nat(nat1, ofs1, len1, nat2, ofs2, nbits) {
	if(nbits == 0) {
		nat2[ofs2] = 0;
		return undefined;
	}

	var wrap = 0;
	for(var i = 0; i < len1; i++) {
			var a = nat1[ofs1+i];
			nat1[ofs1+i] = (a << nbits) | wrap;
			if(nat1[ofs1+i] < 0) nat1[ofs1+i] += 4294967296;
			wrap = a >>> (32 - nbits);
	}

	nat2[ofs2] = wrap;
	if(nat2[ofs2] < 0) nat2[ofs2] += 4294967296;
	return undefined;
}

// Assuming c > a, returns [quotient, remainder] of (a<<32 + b)/c
//Provides: div_helper
function div_helper(a, b, c) {
	var x = a * 65536 + (b>>>16);
	var y = Math.floor(x/c) * 65536;
	var z = (x % c) * 65536;
	var w = z + (b & 0x0000FFFF);
	return [y + Math.floor(w/c), w % c];
}

// nat1[ofs1+len] < nat2[ofs2]
//Provides: div_digit_nat
//Requires: div_helper
function div_digit_nat(natq, ofsq, natr, ofsr, nat1, ofs1, len, nat2, ofs2) {
	var rem = nat1[ofs1+len-1];
	// natq[ofsq+len-1] is guaranteed to be zero (due to the MSD requirement),
	// and should not be written to.
	for(var i = len-2; i >= 0; i--) {
			var x = div_helper(rem, nat1[ofs1+i], nat2[ofs2]);
			natq[ofsq+i] = x[0];
			rem = x[1];
	}
	natr[ofsr] = rem;
	return undefined;
}

// nat1[nat2:] := nat1 / nat2
// nat1[:nat2] := nat1 % nat2
// len1 > len2, nat2[ofs2+len2-1] > nat1[ofs1+len1-1]
//Provides: div_nat
//Requires: div_digit_nat, div_helper, num_leading_zero_bits_in_digit, shift_left_nat, shift_right_nat, create_nat, set_to_zero_nat, mult_digit_nat, sub_nat, compare_nat
function div_nat(nat1, ofs1, len1, nat2, ofs2, len2) {
	if(len2 == 1) {
		div_digit_nat(nat1, ofs1+1, nat1, ofs1, nat1, ofs1, len1, nat2, ofs2);
		return undefined;
	}

	var s = num_leading_zero_bits_in_digit(nat2, ofs2+len2-1);
	shift_left_nat(nat2, ofs2, len2, [0], 0, s);
	shift_left_nat(nat1, ofs1, len1, [0], 0, s);

	var d = nat2[ofs2+len2-1] + 1;
	var a = create_nat(len2+1);
	for (var i = len1 - 1; i >= len2; i--) {
		// Decent lower bound on quo
		var quo = d == 4294967296 ? nat1[ofs1+i] : div_helper(nat1[ofs1+i], nat1[ofs1+i-1], d)[0];
		set_to_zero_nat(a, 0, len2+1);
		mult_digit_nat(a, 0, len2+1, nat2, ofs2, len2, [quo], 0);
		sub_nat(nat1, ofs1+i-len2, len2+1, a, 0, len2+1, 1);

		while (nat1[ofs1+i] != 0 || compare_nat(nat1, ofs1+i-len2, len2, nat2, ofs2, len2) >= 0) {
			quo = quo + 1;
			sub_nat(nat1, ofs1+i-len2, len2+1, nat2, ofs2, len2, 1);
		}

		nat1[ofs1+i] = quo;
	}

	shift_right_nat(nat1, ofs1, len2, [0], 0, s); // shift remainder
	shift_right_nat(nat2, ofs2, len2, [0], 0, s); // restore
	return undefined;
}


// 0 <= shift < 32
//Provides: shift_right_nat
function shift_right_nat(nat1, ofs1, len1, nat2, ofs2, nbits) {
	if(nbits == 0) {
		nat2[ofs2] = 0;
		return undefined;
	}

	var wrap = 0;
	for(var i = len1-1; i >= 0; i--) {
			var a = nat1[ofs1+i];
			nat1[ofs1+i] = (a >>> nbits) | wrap;
			if(nat1[ofs1+i] < 0) nat1[ofs1+i] += 4294967296;
			wrap = a << (32 - nbits);
	}

	nat2[ofs2] = wrap;
	if(nat2[ofs2] < 0) nat2[ofs2] += 4294967296;
	return undefined;
}

//Provides: compare_digits_nat
function compare_digits_nat(nat1, ofs1, nat2, ofs2) {
	if(nat1[ofs1] > nat2[ofs2]) return 1;
	if(nat1[ofs1] < nat2[ofs2]) return -1;
	return 0;
}

//Provides: compare_nat
//Requires: num_digits_nat
function compare_nat(nat1, ofs1, len1, nat2, ofs2, len2) {
	var a = num_digits_nat(nat1, ofs1, len1);
	var b = num_digits_nat(nat2, ofs2, len2);
	if(a > b) return 1;
	if(a < b) return -1;
	for(var i = len1 - 1; i >= 0; i--) {
		if (nat1[ofs1+i] > nat2[ofs2+i]) return 1;
		if (nat1[ofs1+i] < nat2[ofs2+i]) return -1;
	}
	return 0;
}

//Provides: land_digit_nat
function land_digit_nat(nat1, ofs1, nat2, ofs2) {
	nat1[ofs1] &= nat2[ofs2];
	if(nat1[ofs1] < 0) nat1[ofs1] += 4294967296;
	return undefined;
}

//Provides: lor_digit_nat
function lor_digit_nat(nat1, ofs1, nat2, ofs2) {
	nat1[ofs1] |= nat2[ofs2];
	if(nat1[ofs1] < 0) nat1[ofs1] += 4294967296;
	return undefined;
}

//Provides: lxor_digit_nat
function lxor_digit_nat(nat1, ofs1, nat2, ofs2) {
	nat1[ofs1] ^= nat2[ofs2];
	if(nat1[ofs1] < 0) nat1[ofs1] += 4294967296;
	return undefined;
}
/***********************************************************************/
/*                                                                     */
/*                           Objective Caml                            */
/*                                                                     */
/*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 1996 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

/* $Id: lexing.c 6045 2004-01-01 16:42:43Z doligez $ */

/* The table-driven automaton for lexers generated by camllex. */

//Provides: caml_lex_array
//Requires: caml_bytes_of_string
function caml_lex_array(s) {
  s = caml_bytes_of_string(s);
  var l = s.length / 2;
  var a = new Array(l);
  for (var i = 0; i < l; i++)
    a[i] = (s.charCodeAt(2 * i) | (s.charCodeAt(2 * i + 1) << 8)) << 16 >> 16;
  return a;
}

//Provides: caml_lex_engine
//Requires: caml_failwith, caml_lex_array, caml_array_of_string
function caml_lex_engine(tbl, start_state, lexbuf) {
  var lex_buffer = 2;
  var lex_buffer_len = 3;
  var lex_start_pos = 5;
  var lex_curr_pos = 6;
  var lex_last_pos = 7;
  var lex_last_action = 8;
  var lex_eof_reached = 9;
  var lex_base = 1;
  var lex_backtrk = 2;
  var lex_default = 3;
  var lex_trans = 4;
  var lex_check = 5;

  if (!tbl.lex_default) {
    tbl.lex_base =    caml_lex_array (tbl[lex_base]);
    tbl.lex_backtrk = caml_lex_array (tbl[lex_backtrk]);
    tbl.lex_check =   caml_lex_array (tbl[lex_check]);
    tbl.lex_trans =   caml_lex_array (tbl[lex_trans]);
    tbl.lex_default = caml_lex_array (tbl[lex_default]);
  }

  var c, state = start_state;

  var buffer = caml_array_of_string(lexbuf[lex_buffer]);

  if (state >= 0) {
    /* First entry */
    lexbuf[lex_last_pos] = lexbuf[lex_start_pos] = lexbuf[lex_curr_pos];
    lexbuf[lex_last_action] = -1;
  } else {
    /* Reentry after refill */
    state = -state - 1;
  }
  for(;;) {
    /* Lookup base address or action number for current state */
    var base = tbl.lex_base[state];
    if (base < 0) return -base-1;
    /* See if it's a backtrack point */
    var backtrk = tbl.lex_backtrk[state];
    if (backtrk >= 0) {
      lexbuf[lex_last_pos] = lexbuf[lex_curr_pos];
      lexbuf[lex_last_action] = backtrk;
    }
    /* See if we need a refill */
    if (lexbuf[lex_curr_pos] >= lexbuf[lex_buffer_len]){
      if (lexbuf[lex_eof_reached] == 0)
        return -state - 1;
      else
        c = 256;
    }else{
      /* Read next input char */
      c = buffer[lexbuf[lex_curr_pos]];
      lexbuf[lex_curr_pos] ++;
    }
    /* Determine next state */
    if (tbl.lex_check[base + c] == state)
      state = tbl.lex_trans[base + c];
    else
      state = tbl.lex_default[state];
    /* If no transition on this char, return to last backtrack point */
    if (state < 0) {
      lexbuf[lex_curr_pos] = lexbuf[lex_last_pos];
      if (lexbuf[lex_last_action] == -1)
        caml_failwith("lexing: empty token");
      else
        return lexbuf[lex_last_action];
    }else{
      /* Erase the EOF condition only if the EOF pseudo-character was
         consumed by the automaton (i.e. there was no backtrack above)
       */
      if (c == 256) lexbuf[lex_eof_reached] = 0;
    }
  }
}

/***********************************************/
/* New lexer engine, with memory of positions  */
/***********************************************/

//Provides: caml_new_lex_engine
//Requires: caml_failwith, caml_lex_array
//Requires: caml_bytes_of_string, caml_array_of_string
function caml_lex_run_mem(s, i, mem, curr_pos) {
  for (;;) {
    var dst = s.charCodeAt(i); i++;
    if (dst == 0xff) return;
    var src = s.charCodeAt(i); i++;
    if (src == 0xff)
      mem [dst + 1] = curr_pos;
    else
      mem [dst + 1] = mem [src + 1];
  }
}

function caml_lex_run_tag(s, i, mem) {
  for (;;) {
    var dst = s.charCodeAt(i); i++;
    if (dst == 0xff) return ;
    var src = s.charCodeAt(i); i++;
    if (src == 0xff)
      mem [dst + 1] = -1;
    else
      mem [dst + 1] = mem [src + 1];
  }
}

function caml_new_lex_engine(tbl, start_state, lexbuf) {
  var lex_buffer = 2;
  var lex_buffer_len = 3;
  var lex_start_pos = 5;
  var lex_curr_pos = 6;
  var lex_last_pos = 7;
  var lex_last_action = 8;
  var lex_eof_reached = 9;
  var lex_mem = 10;
  var lex_base = 1;
  var lex_backtrk = 2;
  var lex_default = 3;
  var lex_trans = 4;
  var lex_check = 5;
  var lex_base_code = 6;
  var lex_backtrk_code = 7;
  var lex_default_code = 8;
  var lex_trans_code = 9;
  var lex_check_code = 10;
  var lex_code = 11;

  if (!tbl.lex_default) {
    tbl.lex_base =    caml_lex_array (tbl[lex_base]);
    tbl.lex_backtrk = caml_lex_array (tbl[lex_backtrk]);
    tbl.lex_check =   caml_lex_array (tbl[lex_check]);
    tbl.lex_trans =   caml_lex_array (tbl[lex_trans]);
    tbl.lex_default = caml_lex_array (tbl[lex_default]);
  }
  if (!tbl.lex_default_code) {
    tbl.lex_base_code =    caml_lex_array (tbl[lex_base_code]);
    tbl.lex_backtrk_code = caml_lex_array (tbl[lex_backtrk_code]);
    tbl.lex_check_code =   caml_lex_array (tbl[lex_check_code]);
    tbl.lex_trans_code =   caml_lex_array (tbl[lex_trans_code]);
    tbl.lex_default_code = caml_lex_array (tbl[lex_default_code]);
  }
  if (tbl.lex_code == null) tbl.lex_code = caml_bytes_of_string(tbl[lex_code]);

  var c, state = start_state;

  var buffer = caml_array_of_string(lexbuf[lex_buffer]);

  if (state >= 0) {
    /* First entry */
    lexbuf[lex_last_pos] = lexbuf[lex_start_pos] = lexbuf[lex_curr_pos];
    lexbuf[lex_last_action] = -1;
  } else {
    /* Reentry after refill */
    state = -state - 1;
  }
  for(;;) {
    /* Lookup base address or action number for current state */
    var base = tbl.lex_base[state];
    if (base < 0) {
      var pc_off = tbl.lex_base_code[state];
      caml_lex_run_tag(tbl.lex_code, pc_off, lexbuf[lex_mem]);
      return -base-1;
    }
    /* See if it's a backtrack point */
    var backtrk = tbl.lex_backtrk[state];
    if (backtrk >= 0) {
      var pc_off = tbl.lex_backtrk_code[state];
      caml_lex_run_tag(tbl.lex_code, pc_off, lexbuf[lex_mem]);
      lexbuf[lex_last_pos] = lexbuf[lex_curr_pos];
      lexbuf[lex_last_action] = backtrk;
    }
    /* See if we need a refill */
    if (lexbuf[lex_curr_pos] >= lexbuf[lex_buffer_len]){
      if (lexbuf[lex_eof_reached] == 0)
        return -state - 1;
      else
        c = 256;
    }else{
      /* Read next input char */
      c = buffer[lexbuf[lex_curr_pos]];
      lexbuf[lex_curr_pos] ++;
    }
    /* Determine next state */
    var pstate = state ;
    if (tbl.lex_check[base + c] == state)
      state = tbl.lex_trans[base + c];
    else
      state = tbl.lex_default[state];
    /* If no transition on this char, return to last backtrack point */
    if (state < 0) {
      lexbuf[lex_curr_pos] = lexbuf[lex_last_pos];
      if (lexbuf[lex_last_action] == -1)
        caml_failwith("lexing: empty token");
      else
        return lexbuf[lex_last_action];
    }else{
      /* If some transition, get and perform memory moves */
      var base_code = tbl.lex_base_code[pstate], pc_off;
      if (tbl.lex_check_code[base_code + c] == pstate)
        pc_off = tbl.lex_trans_code[base_code + c];
      else
        pc_off = tbl.lex_default_code[pstate];
      if (pc_off > 0)
        caml_lex_run_mem
          (tbl.lex_code, pc_off, lexbuf[lex_mem], lexbuf[lex_curr_pos]);
      /* Erase the EOF condition only if the EOF pseudo-character was
         consumed by the automaton (i.e. there was no backtrack above)
       */
      if (c == 256) lexbuf[lex_eof_reached] = 0;
    }
  }
}

// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010-2014 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

// An OCaml string is an object with three fields:
// - tag 't'
// - length 'l'
// - contents 'c'
//
// The contents of the string can be either a JavaScript array or
// a JavaScript string. The length of this string can be less than the
// length of the OCaml string. In this case, remaining bytes are
// assumed to be zeroes. Arrays are mutable but consumes more memory
// than strings. A common pattern is to start from an empty string and
// progressively fill it from the start. Partial strings makes it
// possible to implement this efficiently.
//
// When converting to and from UTF-16, we keep track of whether the
// string is composed only of ASCII characters (in which case, no
// conversion needs to be performed) or not.
//
// The string tag can thus take the following values:
//   full string     BYTE | UNKNOWN:      0
//                   BYTE | ASCII:        9
//                   BYTE | NOT_ASCII:    8
//   string prefix   PARTIAL:             2
//   array           ARRAY:               4
//
// One can use bit masking to discriminate these different cases:
//   known_encoding(x) = x&8
//   is_ascii(x) =       x&1
//   kind(x) =           x&6

//Provides: caml_str_repeat
function caml_str_repeat(n, s) {
  if (s.repeat) return s.repeat(n); // ECMAscript 6 and Firefox 24+
  var r = "", l = 0;
  if (n == 0) return r;
  for(;;) {
    if (n & 1) r += s;
    n >>= 1;
    if (n == 0) return r;
    s += s;
    l++;
    if (l == 9) {
      s.slice(0,1); // flatten the string
      // then, the flattening of the whole string will be faster,
      // as it will be composed of larger pieces
    }
  }
}

//Provides: caml_subarray_to_string
//Requires: raw_array_sub
function caml_subarray_to_string (a, i, len) {
  var f = String.fromCharCode;
  if (i == 0 && len <= 4096 && len == a.length) return f.apply (null, a);
  var s = "";
  for (; 0 < len; i += 1024,len-=1024)
    s += f.apply (null, raw_array_sub(a,i, Math.min(len, 1024)));
  return s;
}

//Provides: caml_utf8_of_utf16
function caml_utf8_of_utf16(s) {
  for (var b = "", t = b, c, d, i = 0, l = s.length; i < l; i++) {
    c = s.charCodeAt(i);
    if (c < 0x80) {
      for (var j = i + 1; (j < l) && (c = s.charCodeAt(j)) < 0x80; j++);
      if (j - i > 512) { t.substr(0, 1); b += t; t = ""; b += s.slice(i, j) }
      else t += s.slice(i, j);
      if (j == l) break;
      i = j;
    }
    if (c < 0x800) {
      t += String.fromCharCode(0xc0 | (c >> 6));
      t += String.fromCharCode(0x80 | (c & 0x3f));
    } else if (c < 0xd800 || c >= 0xdfff) {
      t += String.fromCharCode(0xe0 | (c >> 12),
                               0x80 | ((c >> 6) & 0x3f),
                               0x80 | (c & 0x3f));
    } else if (c >= 0xdbff || i + 1 == l ||
               (d = s.charCodeAt(i + 1)) < 0xdc00 || d > 0xdfff) {
      // Unmatched surrogate pair, replaced by \ufffd (replacement character)
      t += "\xef\xbf\xbd";
    } else {
      i++;
      c = (c << 10) + d - 0x35fdc00;
      t += String.fromCharCode(0xf0 | (c >> 18),
                               0x80 | ((c >> 12) & 0x3f),
                               0x80 | ((c >> 6) & 0x3f),
                               0x80 | (c & 0x3f));
    }
    if (t.length > 1024) {t.substr(0, 1); b += t; t = "";}
  }
  return b+t;
}

//Provides: caml_utf16_of_utf8
function caml_utf16_of_utf8(s) {
  for (var b = "", t = "", c, c1, c2, v, i = 0, l = s.length; i < l; i++) {
    c1 = s.charCodeAt(i);
    if (c1 < 0x80) {
      for (var j = i + 1; (j < l) && (c1 = s.charCodeAt(j)) < 0x80; j++);
      if (j - i > 512) { t.substr(0, 1); b += t; t = ""; b += s.slice(i, j) }
      else t += s.slice(i, j);
      if (j == l) break;
      i = j;
    }
    v = 1;
    if ((++i < l) && (((c2 = s.charCodeAt(i)) & -64) == 128)) {
      c = c2 + (c1 << 6);
      if (c1 < 0xe0) {
        v = c - 0x3080;
        if (v < 0x80) v = 1;
      } else {
        v = 2;
        if ((++i < l) && (((c2 = s.charCodeAt(i)) & -64) == 128)) {
          c = c2 + (c << 6);
          if (c1 < 0xf0) {
            v = c - 0xe2080;
            if ((v < 0x800) || ((v >= 0xd7ff) && (v < 0xe000))) v = 2;
          } else {
              v = 3;
              if ((++i < l) && (((c2 = s.charCodeAt(i)) & -64) == 128) &&
                  (c1 < 0xf5)) {
                v = c2 - 0x3c82080 + (c << 6);
                if (v < 0x10000 || v > 0x10ffff) v = 3;
              }
          }
        }
      }
    }
    if (v < 4) { // Invalid sequence
      i -= v;
      t += "\ufffd";
    } else if (v > 0xffff)
      t += String.fromCharCode(0xd7c0 + (v >> 10), 0xdc00 + (v & 0x3FF))
    else
      t += String.fromCharCode(v);
    if (t.length > 1024) {t.substr(0, 1); b += t; t = "";}
  }
  return b+t;
}

//Provides: caml_is_ascii
function caml_is_ascii (s) {
  // The regular expression gets better at around this point for all browsers
  if (s.length < 24) {
    // Spidermonkey gets much slower when s.length >= 24 (on 64 bit archs)
    for (var i = 0; i < s.length; i++) if (s.charCodeAt(i) > 127) return false;
    return true;
  } else
    return !/[^\x00-\x7f]/.test(s);
}

//Provides: caml_to_js_string
//Requires: caml_convert_string_to_bytes, caml_is_ascii, caml_utf16_of_utf8
function caml_to_js_string(s) {
  switch (s.t) {
  case 9: /*BYTES | ASCII*/
    return s.c;
  default:
    caml_convert_string_to_bytes(s);
  case 0: /*BYTES | UNKOWN*/
    if (caml_is_ascii(s.c)) {
      s.t = 9; /*BYTES | ASCII*/
      return s.c;
    }
    s.t = 8; /*BYTES | NOT_ASCII*/
  case 8: /*BYTES | NOT_ASCII*/
    return caml_utf16_of_utf8(s.c);
  }
}

//Provides: caml_string_unsafe_get mutable
function caml_string_unsafe_get (s, i) {
  switch (s.t & 6) {
  default: /* PARTIAL */
    if (i >= s.c.length) return 0;
  case 0: /* BYTES */
    return s.c.charCodeAt(i);
  case 4: /* ARRAY */
    return s.c[i]
  }
}

//Provides: caml_bytes_unsafe_get mutable
function caml_bytes_unsafe_get (s, i) {
  switch (s.t & 6) {
  default: /* PARTIAL */
    if (i >= s.c.length) return 0;
  case 0: /* BYTES */
    return s.c.charCodeAt(i);
  case 4: /* ARRAY */
    return s.c[i]
  }
}

//Provides: caml_string_unsafe_set
//Requires: caml_convert_string_to_array
function caml_string_unsafe_set (s, i, c) {
  // The OCaml compiler uses Char.unsafe_chr on integers larger than 255!
  c &= 0xff;
  if (s.t != 4 /* ARRAY */) {
    if (i == s.c.length) {
      s.c += String.fromCharCode (c);
      if (i + 1 == s.l) s.t = 0; /*BYTES | UNKOWN*/
      return 0;
    }
    caml_convert_string_to_array (s);
  }
  s.c[i] = c;
  return 0;
}

//Provides: caml_bytes_unsafe_set
//Requires: caml_convert_string_to_array
function caml_bytes_unsafe_set (s, i, c) {
  // The OCaml compiler uses Char.unsafe_chr on integers larger than 255!
  c &= 0xff;
  if (s.t != 4 /* ARRAY */) {
    if (i == s.c.length) {
      s.c += String.fromCharCode (c);
      if (i + 1 == s.l) s.t = 0; /*BYTES | UNKOWN*/
      return 0;
    }
    caml_convert_string_to_array (s);
  }
  s.c[i] = c;
  return 0;
}

//Provides: caml_string_bound_error
//Requires: caml_invalid_argument
function caml_string_bound_error () {
  caml_invalid_argument ("index out of bounds");
}

//Provides: caml_string_get
//Requires: caml_string_bound_error, caml_string_unsafe_get
function caml_string_get (s, i) {
  if (i >>> 0 >= s.l) caml_string_bound_error();
  return caml_string_unsafe_get (s, i);
}

//Provides: caml_string_get16
//Requires: caml_string_unsafe_get, caml_string_bound_error
function caml_string_get16(s,i) {
  if (i >>> 0 >= s.l + 1) caml_string_bound_error();
  var b1 = caml_string_unsafe_get (s, i),
      b2 = caml_string_unsafe_get (s, i + 1);
  return (b2 << 8 | b1);
}

//Provides: caml_string_get32
//Requires: caml_string_unsafe_get, caml_string_bound_error
function caml_string_get32(s,i) {
  if (i >>> 0 >= s.l + 3) caml_string_bound_error();
  var b1 = caml_string_unsafe_get (s, i),
      b2 = caml_string_unsafe_get (s, i + 1),
      b3 = caml_string_unsafe_get (s, i + 2),
      b4 = caml_string_unsafe_get (s, i + 3);
  return (b4 << 24 | b3 << 16 | b2 << 8 | b1);
}

//Provides: caml_string_get64
//Requires: caml_string_unsafe_get, caml_string_bound_error
//Requires: caml_int64_of_bytes
function caml_string_get64(s,i) {
  if (i >>> 0 >= s.l + 7) caml_string_bound_error();
  var a = new Array(8);
  for(var j = 0; j < 8; j++){
    a[7 - j] = caml_string_unsafe_get (s, i + j);
  }
  return caml_int64_of_bytes(a);
}

//Provides: caml_bytes_get
//Requires: caml_string_bound_error, caml_bytes_unsafe_get
function caml_bytes_get (s, i) {
  if (i >>> 0 >= s.l) caml_string_bound_error();
  return caml_bytes_unsafe_get (s, i);
}

//Provides: caml_string_set
//Requires: caml_string_bound_error, caml_string_unsafe_set
function caml_string_set (s, i, c) {
  if (i >>> 0 >= s.l) caml_string_bound_error();
  return caml_string_unsafe_set (s, i, c);
}

//Provides: caml_string_set16
//Requires: caml_string_bound_error, caml_string_unsafe_set
function caml_string_set16(s,i,i16){
  if (i >>> 0 >= s.l + 1) caml_string_bound_error();
  var b2 = 0xFF & i16 >> 8,
      b1 = 0xFF & i16;
  caml_string_unsafe_set (s, i + 0, b1);
  caml_string_unsafe_set (s, i + 1, b2);
  return 0
}

//Provides: caml_string_set32
//Requires: caml_string_bound_error, caml_string_unsafe_set
function caml_string_set32(s,i,i32){
  if (i >>> 0 >= s.l + 3) caml_string_bound_error();
  var b4 = 0xFF & i32 >> 24,
      b3 = 0xFF & i32 >> 16,
      b2 = 0xFF & i32 >> 8,
      b1 = 0xFF & i32;
  caml_string_unsafe_set (s, i + 0, b1);
  caml_string_unsafe_set (s, i + 1, b2);
  caml_string_unsafe_set (s, i + 2, b3);
  caml_string_unsafe_set (s, i + 3, b4);
  return 0
}

//Provides: caml_string_set64
//Requires: caml_string_bound_error, caml_string_unsafe_set
//Requires: caml_int64_to_bytes
function caml_string_set64(s,i,i64){
  if (i >>> 0 >= s.l + 7) caml_string_bound_error();
  var a = caml_int64_to_bytes(i64);
  for(var j = 0; j < 8; j++) {
    caml_string_unsafe_set (s, i + 7 - j, a[j]);
  }
  return 0
}



//Provides: caml_bytes_set
//Requires: caml_string_bound_error, caml_bytes_unsafe_set
function caml_bytes_set (s, i, c) {
  if (i >>> 0 >= s.l) caml_string_bound_error();
  return caml_bytes_unsafe_set (s, i, c);
}

//Provides: MlString
//Requires: caml_to_js_string
function MlString (tag, contents, length) {
  this.t=tag; this.c=contents; this.l=length;
}
MlString.prototype.toString = function(){return caml_to_js_string(this)};

//Provides: caml_convert_string_to_bytes
//Requires: caml_str_repeat, caml_subarray_to_string
function caml_convert_string_to_bytes (s) {
  /* Assumes not BYTES */
  if (s.t == 2 /* PARTIAL */)
    s.c += caml_str_repeat(s.l - s.c.length, '\0')
  else
    s.c = caml_subarray_to_string (s.c, 0, s.c.length);
  s.t = 0; /*BYTES | UNKOWN*/
}

//Provides: caml_convert_string_to_array
function caml_convert_string_to_array (s) {
  /* Assumes not ARRAY */
  if(joo_global_object.Uint8Array) {
    var a = new joo_global_object.Uint8Array(s.l);
  } else {
    var a = new Array(s.l);
  }
  var b = s.c, l = b.length, i = 0;
  for (; i < l; i++) a[i] = b.charCodeAt(i);
  for (l = s.l; i < l; i++) a[i] = 0;
  s.c = a;
  s.t = 4; /* ARRAY */
  return a;
}

//Provides: caml_array_of_string mutable
//Requires: caml_convert_string_to_array
function caml_array_of_string (s) {
  if (s.t != 4 /* ARRAY */) caml_convert_string_to_array(s);
  return s.c;
}

//Provides: caml_bytes_of_string mutable
//Requires: caml_convert_string_to_bytes
function caml_bytes_of_string (s) {
  if ((s.t & 6) != 0 /* BYTES */) caml_convert_string_to_bytes(s);
  return s.c;
}

//Provides: caml_js_to_string const
//Requires: caml_is_ascii, caml_utf8_of_utf16, MlString
function caml_js_to_string (s) {
  var tag = 9 /* BYTES | ASCII */;
  if (!caml_is_ascii(s))
    tag = 8 /* BYTES | NOT_ASCII */, s = caml_utf8_of_utf16(s);
  return new MlString(tag, s, s.length);
}

//Provides: caml_create_string const
//Requires: MlString,caml_invalid_argument
function caml_create_string(len) {
  if (len < 0) caml_invalid_argument("String.create");
  return new MlString(len?2:9,"",len);
}
//Provides: caml_create_bytes const
//Requires: MlString,caml_invalid_argument
function caml_create_bytes(len) {
  if (len < 0) caml_invalid_argument("Bytes.create");
  return new MlString(len?2:9,"",len);
}

//Provides: caml_new_string
//Requires: MlString
function caml_new_string (s) { return new MlString(0,s,s.length); }
//Provides: caml_string_of_array
//Requires: MlString
function caml_string_of_array (a) { return new MlString(4,a,a.length); }

//Provides: caml_string_compare mutable
//Requires: caml_convert_string_to_bytes
function caml_string_compare(s1, s2) {
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c < s2.c)?-1:(s1.c > s2.c)?1:0;
}


//Provides: caml_bytes_compare mutable
//Requires: caml_convert_string_to_bytes
function caml_bytes_compare(s1, s2) {
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c < s2.c)?-1:(s1.c > s2.c)?1:0;
}

//Provides: caml_string_equal mutable (const, const)
//Requires: caml_convert_string_to_bytes
function caml_string_equal(s1, s2) {
  if(s1 === s2) return 1;
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c == s2.c)?1:0;
}

//Provides: caml_bytes_equal mutable (const, const)
//Requires: caml_convert_string_to_bytes
function caml_bytes_equal(s1, s2) {
  if(s1 === s2) return 1;
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c == s2.c)?1:0;
}

//Provides: caml_string_notequal mutable (const, const)
//Requires: caml_string_equal
function caml_string_notequal(s1, s2) { return 1-caml_string_equal(s1, s2); }

//Provides: caml_bytes_notequal mutable (const, const)
//Requires: caml_string_equal
function caml_bytes_notequal(s1, s2) { return 1-caml_string_equal(s1, s2); }

//Provides: caml_string_lessequal mutable
//Requires: caml_convert_string_to_bytes
function caml_string_lessequal(s1, s2) {
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c <= s2.c)?1:0;
}

//Provides: caml_bytes_lessequal mutable
//Requires: caml_convert_string_to_bytes
function caml_bytes_lessequal(s1, s2) {
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c <= s2.c)?1:0;
}

//Provides: caml_string_lessthan mutable
//Requires: caml_convert_string_to_bytes
function caml_string_lessthan(s1, s2) {
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c < s2.c)?1:0;
}

//Provides: caml_bytes_lessthan mutable
//Requires: caml_convert_string_to_bytes
function caml_bytes_lessthan(s1, s2) {
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c < s2.c)?1:0;
}

//Provides: caml_string_greaterequal
//Requires: caml_string_lessequal
function caml_string_greaterequal(s1, s2) {
  return caml_string_lessequal(s2,s1);
}
//Provides: caml_bytes_greaterequal
//Requires: caml_bytes_lessequal
function caml_bytes_greaterequal(s1, s2) {
  return caml_bytes_lessequal(s2,s1);
}

//Provides: caml_string_greaterthan
//Requires: caml_string_lessthan
function caml_string_greaterthan(s1, s2) {
  return caml_string_lessthan(s2, s1);
}

//Provides: caml_bytes_greaterthan
//Requires: caml_bytes_lessthan
function caml_bytes_greaterthan(s1, s2) {
  return caml_bytes_lessthan(s2, s1);
}

//Provides: caml_fill_string
//Requires: caml_str_repeat, caml_convert_string_to_array
function caml_fill_string(s, i, l, c) {
  if (l > 0) {
    if (i == 0 && (l >= s.l || (s.t == 2 /* PARTIAL */ && l >= s.c.length))) {
      if (c == 0) {
        s.c = "";
        s.t = 2; /* PARTIAL */
      } else {
        s.c = caml_str_repeat (l, String.fromCharCode(c));
        s.t = (l == s.l)?0 /* BYTES | UNKOWN */ :2; /* PARTIAL */
      }
    } else {
      if (s.t != 4 /* ARRAY */) caml_convert_string_to_array(s);
      for (l += i; i < l; i++) s.c[i] = c;
    }
  }
  return 0;
}

//Provides: caml_fill_bytes
//Requires: caml_fill_string
var caml_fill_bytes = caml_fill_string

//Provides: caml_blit_string
//Requires: caml_subarray_to_string, caml_convert_string_to_array
function caml_blit_string(s1, i1, s2, i2, len) {
  if (len == 0) return 0;
  if ((i2 == 0) &&
      (len >= s2.l || (s2.t == 2 /* PARTIAL */ && len >= s2.c.length))) {
    s2.c = (s1.t == 4 /* ARRAY */)?
             caml_subarray_to_string(s1.c, i1, len):
             (i1 == 0 && s1.c.length == len)?s1.c:s1.c.substr(i1, len);
    s2.t = (s2.c.length == s2.l)?0 /* BYTES | UNKOWN */ :2; /* PARTIAL */
  } else if (s2.t == 2 /* PARTIAL */ && i2 == s2.c.length) {
    s2.c += (s1.t == 4 /* ARRAY */)?
             caml_subarray_to_string(s1.c, i1, len):
             (i1 == 0 && s1.c.length == len)?s1.c:s1.c.substr(i1, len);
    s2.t = (s2.c.length == s2.l)?0 /* BYTES | UNKOWN */ :2; /* PARTIAL */
  } else {
    if (s2.t != 4 /* ARRAY */) caml_convert_string_to_array(s2);
    var c1 = s1.c, c2 = s2.c;
    if (s1.t == 4 /* ARRAY */) {
        if (i2 <= i1) {
          for (var i = 0; i < len; i++) c2 [i2 + i] = c1 [i1 + i];
        } else {
          for (var i = len - 1; i >= 0; i--) c2 [i2 + i] = c1 [i1 + i];
        }
   } else {
      var l = Math.min (len, c1.length - i1);
      for (var i = 0; i < l; i++) c2 [i2 + i] = c1.charCodeAt(i1 + i);
      for (; i < len; i++) c2 [i2 + i] = 0;
    }
  }
  return 0;
}

//Provides: caml_blit_bytes
//Requires: caml_blit_string
var caml_blit_bytes = caml_blit_string

//Provides: caml_ml_string_length const
function caml_ml_string_length(s) { return s.l }

//Provides: caml_ml_bytes_length const
function caml_ml_bytes_length(s) { return s.l }
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

///////////// Core

//Provides: raw_array_sub
function raw_array_sub (a,i,l) {
  var b = new Array(l);
  for(var j = 0; j < l; j++) b[j] = a[i+j];
  return b
}

//Provides: raw_array_copy
function raw_array_copy (a) {
  var l = a.length;
  var b = new Array(l);
  for(var i = 0; i < l; i++ ) b[i] = a[i];
  return b
}

//Provides: raw_array_cons
function raw_array_cons (a,x) {
  var l = a.length;
  var b = new Array(l+1);
  b[0]=x;
  for(var i = 1; i <= l; i++ ) b[i] = a[i-1];
  return b
}

//Provides: raw_array_append_one
function raw_array_append_one(a,x) {
  var l = a.length;
  var b = new Array(l+1);
  var i = 0;
  for(; i < l; i++ ) b[i] = a[i];
  b[i]=x;
  return b
}

//Provides: caml_call_gen (const, shallow)
//Requires: raw_array_sub
//Requires: raw_array_append_one
function caml_call_gen(f, args) {
  if(f.fun)
    return caml_call_gen(f.fun, args);
  var n = f.length;
  var argsLen = args.length;
  var d = n - argsLen;
  if (d == 0)
    return f.apply(null, args);
  else if (d < 0)
    return caml_call_gen(f.apply(null,
                                 raw_array_sub(args,0,n)),
                         raw_array_sub(args,n,argsLen - n));
  else
    return function (x){ return caml_call_gen(f, raw_array_append_one(args,x)); };
}

//Provides: caml_named_values
var caml_named_values = {};

//Provides: caml_register_named_value (const,const)
//Requires: caml_named_values, caml_bytes_of_string
function caml_register_named_value(nm,v) {
  caml_named_values[caml_bytes_of_string(nm)] = v;
  return 0;
}

//Provides: caml_named_value
//Requires: caml_named_values
function caml_named_value(nm) {
  return caml_named_values[nm]
}

//Provides: caml_global_data
var caml_global_data = [0];

//Provides: caml_register_global (const, shallow, const)
//Requires: caml_global_data
function caml_register_global (n, v, name_opt) {
  caml_global_data[n + 1] = v;
  if(name_opt) caml_global_data[name_opt] = v;
}

//Provides: caml_get_global_data mutable
//Requires: caml_global_data
function caml_get_global_data () { return caml_global_data; }

//Raise exception


//Provides: caml_raise_constant (const)
//Version: < 4.02
function caml_raise_constant (tag) { throw [0, tag]; }

//Provides: caml_raise_constant (const)
//Version: >= 4.02
function caml_raise_constant (tag) { throw tag; }

//Provides: caml_return_exn_constant (const)
//Version: < 4.02
function caml_return_exn_constant (tag) { return [0, tag]; }

//Provides: caml_return_exn_constant (const)
//Version: >= 4.02
function caml_return_exn_constant (tag) { return tag; }

//Provides: caml_raise_with_arg (const, const)
function caml_raise_with_arg (tag, arg) { throw [0, tag, arg]; }

//Provides: caml_raise_with_string (const, const)
//Requires: caml_raise_with_arg,caml_new_string
function caml_raise_with_string (tag, msg) {
  caml_raise_with_arg (tag, caml_new_string (msg));
}

//Provides: caml_raise_sys_error (const)
//Requires: caml_raise_with_string, caml_global_data
function caml_raise_sys_error (msg) {
  caml_raise_with_string(caml_global_data.Sys_error, msg);
}

//Provides: caml_failwith (const)
//Requires: caml_raise_with_string, caml_global_data
function caml_failwith (msg) {
  caml_raise_with_string(caml_global_data.Failure, msg);
}

//Provides: caml_wrap_exception const (const)
//Requires: caml_global_data,caml_js_to_string,caml_named_value
//Requires: caml_return_exn_constant
function caml_wrap_exception(e) {
  if(e instanceof Array) return e;
  //Stack_overflow: chrome, safari
  if(joo_global_object.RangeError
     && e instanceof joo_global_object.RangeError
     && e.message
     && e.message.match(/maximum call stack/i))
    return caml_return_exn_constant(caml_global_data.Stack_overflow);
  //Stack_overflow: firefox
  if(joo_global_object.InternalError
     && e instanceof joo_global_object.InternalError
     && e.message
     && e.message.match(/too much recursion/i))
    return caml_return_exn_constant(caml_global_data.Stack_overflow);
  //Wrap Error in Js.Error exception
  if(e instanceof joo_global_object.Error)
    return [0,caml_named_value("jsError"),e];
  //fallback: wrapped in Failure
  return [0,caml_global_data.Failure,caml_js_to_string (String(e))];
}

// Experimental
//Provides: caml_exn_with_js_backtrace
//Requires: caml_global_data
function caml_exn_with_js_backtrace(exn, force) {
  if(!exn.js_error || force) exn.js_error = new joo_global_object.Error("Js exception containing backtrace");
  return exn;
}
//Provides: caml_js_error_of_exception
function caml_js_error_of_exception(exn) {
  if(exn.js_error) { return exn.js_error; }
  return null;
}

//Provides: caml_invalid_argument (const)
//Requires: caml_raise_with_string, caml_global_data
function caml_invalid_argument (msg) {
  caml_raise_with_string(caml_global_data.Invalid_argument, msg);
}

//Provides: caml_raise_end_of_file
//Requires: caml_raise_constant, caml_global_data
function caml_raise_end_of_file () {
  caml_raise_constant(caml_global_data.End_of_file);
}

//Provides: caml_raise_zero_divide
//Requires: caml_raise_constant, caml_global_data
function caml_raise_zero_divide () {
  caml_raise_constant(caml_global_data.Division_by_zero);
}

//Provides: caml_raise_not_found
//Requires: caml_raise_constant, caml_global_data
function caml_raise_not_found () {
  caml_raise_constant(caml_global_data.Not_found); }


//Provides: caml_array_bound_error
//Requires: caml_invalid_argument
function caml_array_bound_error () {
  caml_invalid_argument("index out of bounds");
}

//Provides: caml_update_dummy
function caml_update_dummy (x, y) {
  if( typeof y==="function" ) { x.fun = y; return 0; }
  if( y.fun ) { x.fun = y.fun; return 0; }
  var i = y.length; while (i--) x[i] = y[i]; return 0;
}

//Provides: caml_obj_is_block const (const)
function caml_obj_is_block (x) { return +(x instanceof Array); }
//Provides: caml_obj_tag const (const)
//Requires: MlString
function caml_obj_tag (x) { return (x instanceof Array)?x[0]:(x instanceof MlString)?252:1000; }
//Provides: caml_obj_set_tag (mutable, const)
function caml_obj_set_tag (x, tag) { x[0] = tag; return 0; }
//Provides: caml_obj_block const (const,const)
function caml_obj_block (tag, size) {
  var o = new Array(size+1);
  o[0]=tag;
  for (var i = 1; i <= size; i++) o[i] = 0;
  return o;
}
//Provides: caml_obj_dup mutable (const)
function caml_obj_dup (x) {
  var l = x.length;
  var a = new Array(l);
  for(var i = 0; i < l; i++ ) a[i] = x[i];
  return a;
}
//Provides: caml_obj_truncate (mutable, const)
//Requires: caml_invalid_argument
function caml_obj_truncate (x, s) {
  if (s<=0 || s + 1 > x.length)
    caml_invalid_argument ("Obj.truncate");
  if (x.length != s + 1) x.length = s + 1;
  return 0;
}

//Provides: caml_lazy_make_forward const (const)
function caml_lazy_make_forward (v) { return [250, v]; }

//Provides: caml_mul const
if (!Math.imul)
  Math.imul =
    function (x,y)
    { y |= 0; return ((((x >> 16) * y) << 16) + (x & 0xffff) * y)|0; };
var caml_mul = Math.imul;

//slightly slower
// function mul32(x,y) {
//   var xlo = x & 0xffff;
//   var xhi = x - xlo;
//   return (((xhi * y) |0) + xlo * y)|0;
// }

//Provides: caml_div
//Requires: caml_raise_zero_divide
function caml_div(x,y) {
  if (y == 0) caml_raise_zero_divide ();
  return (x/y)|0;
}

//Provides: caml_mod
//Requires: caml_raise_zero_divide
function caml_mod(x,y) {
  if (y == 0) caml_raise_zero_divide ();
  return x%y;
}

///////////// Pervasive
//Provides: caml_array_set (mutable, const, const)
//Requires: caml_array_bound_error
function caml_array_set (array, index, newval) {
  if ((index < 0) || (index >= array.length - 1)) caml_array_bound_error();
  array[index+1]=newval; return 0;
}

//Provides: caml_array_get mutable (const, const)
//Requires: caml_array_bound_error
function caml_array_get (array, index) {
  if ((index < 0) || (index >= array.length - 1)) caml_array_bound_error();
  return array[index+1];
}

//Provides: caml_check_bound (const, const)
//Requires: caml_array_bound_error
function caml_check_bound (array, index) {
  if (index >>> 0 >= array.length - 1) caml_array_bound_error();
  return array;
}

//Provides: caml_make_vect const (const, const)
function caml_make_vect (len, init) {
  var len = len + 1 | 0;
  var b = new Array(len);
  b[0]=0;
  for (var i = 1; i < len; i++) b[i] = init;
  return b;
}

//Provides: caml_make_float_vect const (const)
function caml_make_float_vect(len){
  var len = len + 1 | 0;
  var b = new Array(len);
  b[0]=254;
  for (var i = 1; i < len; i++) b[i] = 0;
  return b
}

//Provides: caml_compare_val (const, const, const)
//Requires: MlString, caml_int64_compare, caml_int_compare, caml_string_compare
//Requires: caml_invalid_argument
function caml_compare_val (a, b, total) {
  var stack = [];
  for(;;) {
    if (!(total && a === b)) {
      if (a instanceof MlString) {
        if (b instanceof MlString) {
            if (a !== b) {
		var x = caml_string_compare(a, b);
		if (x != 0) return x;
	    }
        } else
          // Should not happen
          return 1;
      } else if (a instanceof Array && a[0] === (a[0]|0)) {
        var ta = a[0];
        // ignore double_array_tag
        if (ta === 254) ta=0;
        // Forward object
        if (ta === 250) {
          a = a[1];
          continue;
        } else if (b instanceof Array && b[0] === (b[0]|0)) {
          var tb = b[0];
          // ignore double_array_tag
          if (tb === 254) tb=0;
          // Forward object
          if (tb === 250) {
            b = b[1];
            continue;
          } else if (ta != tb) {
            return (ta < tb)?-1:1;
          } else {
            switch (ta) {
            case 248: {
		// Object
		var x = caml_int_compare(a[2], b[2]);
		if (x != 0) return x;
		break;
	    }
            case 251: {
                caml_invalid_argument("equal: abstract value");
            }
            case 255: {
		// Int64
		var x = caml_int64_compare(a, b);
		if (x != 0) return x;
		break;
	    }
            default:
              if (a.length != b.length) return (a.length < b.length)?-1:1;
              if (a.length > 1) stack.push(a, b, 1);
            }
          }
        } else
          return 1;
      } else if (b instanceof MlString ||
                 (b instanceof Array && b[0] === (b[0]|0))) {
        return -1;
      } else if (typeof a != "number" && a && a.compare) {
        return a.compare(b,total);
      } else if (typeof a == "function") {
        caml_invalid_argument("equal: functional value");
      } else {
        if (a < b) return -1;
        if (a > b) return 1;
        if (a != b) {
          if (!total) return NaN;
          if (a == a) return 1;
          if (b == b) return -1;
        }
      }
    }
    if (stack.length == 0) return 0;
    var i = stack.pop();
    b = stack.pop();
    a = stack.pop();
    if (i + 1 < a.length) stack.push(a, b, i + 1);
    a = a[i];
    b = b[i];
  }
}
//Provides: caml_compare (const, const)
//Requires: caml_compare_val
function caml_compare (a, b) { return caml_compare_val (a, b, true); }
//Provides: caml_int_compare mutable (const, const)
function caml_int_compare (a, b) {
  if (a < b) return (-1); if (a == b) return 0; return 1;
}
//Provides: caml_equal mutable (const, const)
//Requires: caml_compare_val
function caml_equal (x, y) { return +(caml_compare_val(x,y,false) == 0); }
//Provides: caml_notequal mutable (const, const)
//Requires: caml_compare_val
function caml_notequal (x, y) { return +(caml_compare_val(x,y,false) != 0); }
//Provides: caml_greaterequal mutable (const, const)
//Requires: caml_compare_val
function caml_greaterequal (x, y) { return +(caml_compare_val(x,y,false) >= 0); }
//Provides: caml_greaterthan mutable (const, const)
//Requires: caml_compare_val
function caml_greaterthan (x, y) { return +(caml_compare_val(x,y,false) > 0); }
//Provides: caml_lessequal mutable (const, const)
//Requires: caml_compare_val
function caml_lessequal (x, y) { return +(caml_compare_val(x,y,false) <= 0); }
//Provides: caml_lessthan mutable (const, const)
//Requires: caml_compare_val
function caml_lessthan (x, y) { return +(caml_compare_val(x,y,false) < 0); }

//Provides: caml_parse_sign_and_base
//Requires: caml_string_unsafe_get, caml_ml_string_length
function caml_parse_sign_and_base (s) {
  var i = 0, len = caml_ml_string_length(s), base = 10,
     sign = (len > 0 && caml_string_unsafe_get(s,0) == 45)?(i++,-1):1;
  if (i + 1 < len && caml_string_unsafe_get(s, i) == 48)
    switch (caml_string_unsafe_get(s, i + 1)) {
    case 120: case 88: base = 16; i += 2; break;
    case 111: case 79: base =  8; i += 2; break;
    case  98: case 66: base =  2; i += 2; break;
    }
  return [i, sign, base];
}

//Provides: caml_parse_digit
function caml_parse_digit(c) {
  if (c >= 48 && c <= 57)  return c - 48;
  if (c >= 65 && c <= 90)  return c - 55;
  if (c >= 97 && c <= 122) return c - 87;
  return -1;
}

//Provides: caml_int_of_string (const)
//Requires: caml_ml_string_length, caml_string_unsafe_get
//Requires: caml_parse_sign_and_base, caml_parse_digit, caml_failwith
function caml_int_of_string (s) {
  var r = caml_parse_sign_and_base (s);
  var i = r[0], sign = r[1], base = r[2];
  var len = caml_ml_string_length(s);
  var threshold = -1 >>> 0;
  var c = (i < len)?caml_string_unsafe_get(s, i):0;
  var d = caml_parse_digit(c);
  if (d < 0 || d >= base) caml_failwith("int_of_string");
  var res = d;
  for (i++;i<len;i++) {
    c = caml_string_unsafe_get(s, i);
    if (c == 95) continue;
    d = caml_parse_digit(c);
    if (d < 0 || d >= base) break;
    res = base * res + d;
    if (res > threshold) caml_failwith("int_of_string");
  }
  if (i != len) caml_failwith("int_of_string");
  // For base different from 10, we expect an unsigned representation,
  // hence any value of 'res' (less than 'threshold') is acceptable.
  // But we have to convert the result back to a signed integer.
  res = sign * res;
  if ((base == 10) && ((res | 0) != res))
    /* Signed representation expected, allow -2^(nbits-1) to 2^(nbits-1) - 1 */
    caml_failwith("int_of_string");
  return res | 0;
}

//Provides: caml_float_of_string (const)
//Requires: caml_failwith, caml_bytes_of_string
function caml_float_of_string(s) {
  var res;
  s = caml_bytes_of_string (s);
  res = +s;
  if ((s.length > 0) && (res === res)) return res;
  s = s.replace(/_/g,"");
  res = +s;
  if (((s.length > 0) && (res === res)) || /^[+-]?nan$/i.test(s)) return res;
  var m = /^ *([+-]?)0x([0-9a-f]+)\.?([0-9a-f]*)p([+-]?[0-9]+)/i.exec(s);
//            1        2             3           4
  if(m){
    var m3 = m[3].replace(/0+$/,'');
    var mantissa = parseInt(m[1] + m[2] + m3, 16);
    var exponent = (m[4]|0) - 4*m3.length;
    res = mantissa * Math.pow(2, exponent);
    return res;
  }
  if(/^\+?inf(inity)?$/i.test(s)) return Infinity;
  if(/^-inf(inity)?$/i.test(s)) return -Infinity;
  caml_failwith("float_of_string");
}

//Provides: caml_is_printable const (const)
function caml_is_printable(c) { return +(c > 31 && c < 127); }

///////////// Format
//Provides: caml_parse_format
//Requires: caml_bytes_of_string, caml_invalid_argument
function caml_parse_format (fmt) {
  fmt = caml_bytes_of_string(fmt);
  var len = fmt.length;
  if (len > 31) caml_invalid_argument("format_int: format too long");
  var f =
    { justify:'+', signstyle:'-', filler:' ', alternate:false,
      base:0, signedconv:false, width:0, uppercase:false,
      sign:1, prec:-1, conv:'f' };
  for (var i = 0; i < len; i++) {
    var c = fmt.charAt(i);
    switch (c) {
    case '-':
      f.justify = '-'; break;
    case '+': case ' ':
      f.signstyle = c; break;
    case '0':
      f.filler = '0'; break;
    case '#':
      f.alternate = true; break;
    case '1': case '2': case '3': case '4': case '5':
    case '6': case '7': case '8': case '9':
      f.width = 0;
      while (c=fmt.charCodeAt(i) - 48, c >= 0 && c <= 9) {
        f.width = f.width * 10 + c; i++
      }
      i--;
     break;
    case '.':
      f.prec = 0;
      i++;
      while (c=fmt.charCodeAt(i) - 48, c >= 0 && c <= 9) {
        f.prec = f.prec * 10 + c; i++
      }
      i--;
    case 'd': case 'i':
      f.signedconv = true; /* fallthrough */
    case 'u':
      f.base = 10; break;
    case 'x':
      f.base = 16; break;
    case 'X':
      f.base = 16; f.uppercase = true; break;
    case 'o':
      f.base = 8; break;
    case 'e': case 'f': case 'g':
      f.signedconv = true; f.conv = c; break;
    case 'E': case 'F': case 'G':
      f.signedconv = true; f.uppercase = true;
      f.conv = c.toLowerCase (); break;
    }
  }
  return f;
}

//Provides: caml_finish_formatting
//Requires: caml_new_string
function caml_finish_formatting(f, rawbuffer) {
  if (f.uppercase) rawbuffer = rawbuffer.toUpperCase();
  var len = rawbuffer.length;
  /* Adjust len to reflect additional chars (sign, etc) */
  if (f.signedconv && (f.sign < 0 || f.signstyle != '-')) len++;
  if (f.alternate) {
    if (f.base == 8) len += 1;
    if (f.base == 16) len += 2;
  }
  /* Do the formatting */
  var buffer = "";
  if (f.justify == '+' && f.filler == ' ')
    for (var i = len; i < f.width; i++) buffer += ' ';
  if (f.signedconv) {
    if (f.sign < 0) buffer += '-';
    else if (f.signstyle != '-') buffer += f.signstyle;
  }
  if (f.alternate && f.base == 8) buffer += '0';
  if (f.alternate && f.base == 16) buffer += "0x";
  if (f.justify == '+' && f.filler == '0')
    for (var i = len; i < f.width; i++) buffer += '0';
  buffer += rawbuffer;
  if (f.justify == '-')
    for (var i = len; i < f.width; i++) buffer += ' ';
  return caml_new_string (buffer);
}

//Provides: caml_format_int const (const, const)
//Requires: caml_parse_format, caml_finish_formatting, caml_str_repeat
//Requires: caml_new_string, caml_bytes_of_string
function caml_format_int(fmt, i) {
  if (caml_bytes_of_string(fmt) == "%d") return caml_new_string(""+i);
  var f = caml_parse_format(fmt);
  if (i < 0) { if (f.signedconv) { f.sign = -1; i = -i; } else i >>>= 0; }
  var s = i.toString(f.base);
  if (f.prec >= 0) {
    f.filler = ' ';
    var n = f.prec - s.length;
    if (n > 0) s = caml_str_repeat (n, '0') + s;
  }
  return caml_finish_formatting(f, s);
}

//Provides: caml_format_float const
//Requires: caml_parse_format, caml_finish_formatting
function caml_format_float (fmt, x) {
  var s, f = caml_parse_format(fmt);
  var prec = (f.prec < 0)?6:f.prec;
  if (x < 0 || (x == 0 && 1/x == -Infinity)) { f.sign = -1; x = -x; }
  if (isNaN(x)) { s = "nan"; f.filler = ' '; }
  else if (!isFinite(x)) { s = "inf"; f.filler = ' '; }
  else
    switch (f.conv) {
    case 'e':
      var s = x.toExponential(prec);
      // exponent should be at least two digits
      var i = s.length;
      if (s.charAt(i - 3) == 'e')
        s = s.slice (0, i - 1) + '0' + s.slice (i - 1);
      break;
    case 'f':
      s = x.toFixed(prec); break;
    case 'g':
      prec = prec?prec:1;
      s = x.toExponential(prec - 1);
      var j = s.indexOf('e');
      var exp = +s.slice(j + 1);
      if (exp < -4 || x >= 1e21 || x.toFixed(0).length > prec) {
        // remove trailing zeroes
        var i = j - 1; while (s.charAt(i) == '0') i--;
        if (s.charAt(i) == '.') i--;
        s = s.slice(0, i + 1) + s.slice(j);
        i = s.length;
        if (s.charAt(i - 3) == 'e')
          s = s.slice (0, i - 1) + '0' + s.slice (i - 1);
        break;
      } else {
        var p = prec;
        if (exp < 0) { p -= exp + 1; s = x.toFixed(p); }
        else while (s = x.toFixed(p), s.length > prec + 1) p--;
        if (p) {
          // remove trailing zeroes
          var i = s.length - 1; while (s.charAt(i) == '0') i--;
          if (s.charAt(i) == '.') i--;
          s = s.slice(0, i + 1);
        }
      }
      break;
    }
  return caml_finish_formatting(f, s);
}

///////////// Hashtbl
//Provides: caml_hash_univ_param mutable
//Requires: MlString, caml_convert_string_to_bytes
//Requires: caml_int64_to_bytes, caml_int64_bits_of_float
function caml_hash_univ_param (count, limit, obj) {
  var hash_accu = 0;
  function hash_aux (obj) {
    limit --;
    if (count < 0 || limit < 0) return;
    if (obj instanceof Array && obj[0] === (obj[0]|0)) {
      switch (obj[0]) {
      case 248:
        // Object
        count --;
        hash_accu = (hash_accu * 65599 + obj[2]) | 0;
        break;
      case 250:
        // Forward
        limit++; hash_aux(obj); break;
      case 255:
        // Int64
        count --;
        hash_accu = (hash_accu * 65599 + obj[1] + (obj[2] << 24)) | 0;
        break;
      default:
        count --;
        hash_accu = (hash_accu * 19 + obj[0]) | 0;
        for (var i = obj.length - 1; i > 0; i--) hash_aux (obj[i]);
      }
    } else if (obj instanceof MlString) {
      count --;
      switch (obj.t & 6) {
      default: /* PARTIAL */
        caml_convert_string_to_bytes(obj);
      case 0: /* BYTES */
        for (var b = obj.c, l = obj.l, i = 0; i < l; i++)
          hash_accu = (hash_accu * 19 + b.charCodeAt(i)) | 0;
        break;
      case 2: /* ARRAY */
        for (var a = obj.c, l = obj.l, i = 0; i < l; i++)
          hash_accu = (hash_accu * 19 + a[i]) | 0;
      }
    } else if (obj === (obj|0)) {
      // Integer
      count --;
      hash_accu = (hash_accu * 65599 + obj) | 0;
    } else if (obj === +obj) {
      // Float
      count--;
      var p = caml_int64_to_bytes (caml_int64_bits_of_float (obj));
      for (var i = 7; i >= 0; i--) hash_accu = (hash_accu * 19 + p[i]) | 0;
    }
  }
  hash_aux (obj);
  return hash_accu & 0x3FFFFFFF;
}

//function ROTL32(x,n) { return ((x << n) | (x >>> (32-n))); }
//Provides: caml_hash_mix_int
//Requires: caml_mul
function caml_hash_mix_int(h,d) {
  d = caml_mul(d, 0xcc9e2d51|0);
  d = ((d << 15) | (d >>> (32-15))); // ROTL32(d, 15);
  d = caml_mul(d, 0x1b873593);
  h ^= d;
  h = ((h << 13) | (h >>> (32-13)));   //ROTL32(h, 13);
  return (((h + (h << 2))|0) + (0xe6546b64|0))|0;
}

//Provides: caml_hash_mix_final
//Requires: caml_mul
function caml_hash_mix_final(h) {
  h ^= h >>> 16;
  h = caml_mul (h, 0x85ebca6b|0);
  h ^= h >>> 13;
  h = caml_mul (h, 0xc2b2ae35|0);
  h ^= h >>> 16;
  return h;
}

//Provides: caml_hash_mix_float
//Requires: caml_hash_mix_int, caml_int64_bits_of_float
function caml_hash_mix_float (h, v0) {
  var v = caml_int64_bits_of_float (v0);
  var lo = v[1] | (v[2] << 24);
  var hi = (v[2] >>> 8) | (v[3] << 16);
  h = caml_hash_mix_int(h, lo);
  h = caml_hash_mix_int(h, hi);
  return h;
}
//Provides: caml_hash_mix_int64
//Requires: caml_hash_mix_int
function caml_hash_mix_int64 (h, v) {
  var lo = v[1] | (v[2] << 24);
  var hi = (v[2] >>> 8) | (v[3] << 16);
  h = caml_hash_mix_int(h, hi ^ lo);
  return h;
}

//Provides: caml_hash_mix_string_str
//Requires: caml_hash_mix_int
function caml_hash_mix_string_str(h, s) {
  var len = s.length, i, w;
  for (i = 0; i + 4 <= len; i += 4) {
    w = s.charCodeAt(i)
        | (s.charCodeAt(i+1) << 8)
        | (s.charCodeAt(i+2) << 16)
        | (s.charCodeAt(i+3) << 24);
    h = caml_hash_mix_int(h, w);
  }
  w = 0;
  switch (len & 3) {
  case 3: w  = s.charCodeAt(i+2) << 16;
  case 2: w |= s.charCodeAt(i+1) << 8;
  case 1: w |= s.charCodeAt(i);
          h = caml_hash_mix_int(h, w);
  default:
  }
  h ^= len;
  return h;
}

//Provides: caml_hash_mix_string_arr
//Requires: caml_hash_mix_int
function caml_hash_mix_string_arr(h, s) {
  var len = s.length, i, w;
  for (i = 0; i + 4 <= len; i += 4) {
    w = s[i]
      | (s[i+1] << 8)
      | (s[i+2] << 16)
      | (s[i+3] << 24);
    h = caml_hash_mix_int(h, w);
  }
  w = 0;
  switch (len & 3) {
  case 3: w  = s[i+2] << 16;
  case 2: w |= s[i+1] << 8;
  case 1: w |= s[i];
    h = caml_hash_mix_int(h, w);
  default:
  }
  h ^= len;
  return h;
}

//Provides: caml_hash_mix_string
//Requires: caml_convert_string_to_bytes
//Requires: caml_hash_mix_string_str
//Requires: caml_hash_mix_string_arr
function caml_hash_mix_string(h, v) {
    switch (v.t & 6) {
    default:
        caml_convert_string_to_bytes (v);
    case 0: /* BYTES */
        h = caml_hash_mix_string_str(h, v.c);
        break;
    case 2: /* ARRAY */
        h = caml_hash_mix_string_arr(h, v.c);
    }
    return h
}


//Provides: caml_hash mutable
//Requires: MlString
//Requires: caml_int64_bits_of_float, caml_hash_mix_int, caml_hash_mix_final
//Requires: caml_hash_mix_int64, caml_hash_mix_float, caml_hash_mix_string
var HASH_QUEUE_SIZE = 256;
function caml_hash (count, limit, seed, obj) {
    var queue, rd, wr, sz, num, h, v, i, len;
    sz = limit;
    if (sz < 0 || sz > HASH_QUEUE_SIZE) sz = HASH_QUEUE_SIZE;
    num = count;
    h = seed;
    queue = [obj]; rd = 0; wr = 1;
    while (rd < wr && num > 0) {
        v = queue[rd++];
        if (v instanceof Array && v[0] === (v[0]|0)) {
            switch (v[0]) {
            case 248:
                // Object
                h = caml_hash_mix_int(h, v[2]);
                num--;
                break;
            case 250:
                // Forward
                queue[--rd] = v[1];
                break;
            case 255:
                // Int64
                h = caml_hash_mix_int64 (h, v);
                num --;
                break;
            default:
                var tag = ((v.length - 1) << 10) | v[0];
                h = caml_hash_mix_int(h, tag);
                for (i = 1, len = v.length; i < len; i++) {
                    if (wr >= sz) break;
                    queue[wr++] = v[i];
                }
                break;
            }
        } else if (v instanceof MlString) {
            h = caml_hash_mix_string(h,v)
            num--;
        } else if (v === (v|0)) {
            // Integer
            h = caml_hash_mix_int(h, v+v+1);
            num--;
        } else if (v === +v) {
            // Float
            h = caml_hash_mix_float(h,v);
            num--;
        }
    }
    h = caml_hash_mix_final(h);
    return h & 0x3FFFFFFF;
}

///////////// Sys
//Provides: caml_sys_time mutable
var caml_initial_time = new Date() * 0.001;
function caml_sys_time () { return new Date() * 0.001 - caml_initial_time; }
//Provides: caml_sys_get_config const
//Requires: caml_new_string
function caml_sys_get_config () {
  return [0, caml_new_string("Unix"), 32, 0];
}

//Provides: caml_sys_const_backend_type const
//Requires: caml_new_string
function caml_sys_const_backend_type () {
  return [0, caml_new_string("js_of_ocaml")];
}


//Provides: caml_sys_random_seed mutable
//Version: < 4.00
//The function needs to return an array since OCaml 4.0...
function caml_sys_random_seed () {
  var x = new Date()^0xffffffff*Math.random();
  return x;
}

//Provides: caml_sys_random_seed mutable
//Version: >= 4.00
//The function needs to return an array since OCaml 4.0...
function caml_sys_random_seed () {
  var x = new Date()^0xffffffff*Math.random();
  return [0,x];
}



//Provides: caml_sys_const_big_endian const
function caml_sys_const_big_endian () { return 0; }
//Provides: caml_sys_const_word_size const
function caml_sys_const_word_size () { return 32; }
//Provides: caml_sys_const_int_size const
function caml_sys_const_int_size () { return 32; }

//Provides: caml_sys_const_max_wosize const
// max_int / 4 so that the following does not overflow
//let max_string_length = word_size / 8 * max_array_length - 1;;
function caml_sys_const_max_wosize () { return (0x7FFFFFFF/4) | 0;}

//Provides: caml_sys_const_ostype_cygwin const
function caml_sys_const_ostype_cygwin () { return 0; }
//Provides: caml_sys_const_ostype_unix const
function caml_sys_const_ostype_unix () { return 1; }
//Provides: caml_sys_const_ostype_win32 const
function caml_sys_const_ostype_win32 () { return 0; }

//Provides: caml_sys_system_command
function caml_sys_system_command(cmd){
  var cmd = cmd.toString();
  joo_global_object.console.log(cmd);
  if (typeof require != "undefined"
      && require('child_process')
      && require('child_process').execSync) {
    try {require('child_process').execSync(cmd); return 0}
    catch (e) {return 1}
  }
  else return 127;
}

///////////// Array
//Provides: caml_array_sub mutable
function caml_array_sub (a, i, len) {
  var a2 = new Array(len+1);
  a2[0]=0;
  for(var i2 = 1, i1= i+1; i2 <= len; i2++,i1++ ){
    a2[i2]=a[i1];
  }
  return a2;
}

//Provides: caml_array_append mutable
function caml_array_append(a1, a2) {
  var l1 = a1.length, l2 = a2.length;
  var l = l1+l2-1
  var a = new Array(l);
  a[0] = 0;
  var i = 1,j = 1;
  for(;i<l1;i++) a[i]=a1[i];
  for(;i<l;i++,j++) a[i]=a2[j];
  return a;
}

//Provides: caml_array_concat mutable
function caml_array_concat(l) {
  var a = [0];
  while (l !== 0) {
    var b = l[1];
    for (var i = 1; i < b.length; i++) a.push(b[i]);
    l = l[2];
  }
  return a;
}

//Provides: caml_array_blit
function caml_array_blit(a1, i1, a2, i2, len) {
  if (i2 <= i1) {
    for (var j = 1; j <= len; j++) a2[i2 + j] = a1[i1 + j];
  } else {
    for (var j = len; j >= 1; j--) a2[i2 + j] = a1[i1 + j];
  };
  return 0;
}

///////////// CamlinternalOO
//Provides: caml_get_public_method const
var caml_method_cache = [];
function caml_get_public_method (obj, tag, cacheid) {
  var meths = obj[1];
  var ofs = caml_method_cache[cacheid];
  if (ofs === null) {
    // Make sure the array is not sparse
    for (var i = caml_method_cache.length; i < cacheid; i++)
      caml_method_cache[i] = 0;
  } else if (meths[ofs] === tag) {
    return meths[ofs - 1];
  }
  var li = 3, hi = meths[1] * 2 + 1, mi;
  while (li < hi) {
    mi = ((li+hi) >> 1) | 1;
    if (tag < meths[mi+1]) hi = mi-2;
    else li = mi;
  }
  caml_method_cache[cacheid] = li + 1;
  /* return 0 if tag is not there */
  return (tag == meths[li+1] ? meths[li] : 0);
}

//Provides: caml_final_register const
function caml_final_register () { return 0; }
//Provides: caml_final_register_called_without_value const
function caml_final_register_called_without_value () { return 0; }
//Provides: caml_final_release const
function caml_final_release () { return 0; }
//Provides: caml_backtrace_status const
function caml_backtrace_status () { return 0; }
//Provides: caml_get_exception_backtrace const
function caml_get_exception_backtrace () { return 0; }
//Provides: caml_get_exception_raw_backtrace const
function caml_get_exception_raw_backtrace () { return [0]; }
//Provides: caml_record_backtrace
function caml_record_backtrace () { return 0; }
//Provides: caml_convert_raw_backtrace const
function caml_convert_raw_backtrace () { return 0; }
//Provides: caml_raw_backtrace_length
function caml_raw_backtrace_length() { return 0; }
//Provides: caml_raw_backtrace_next_slot
function caml_raw_backtrace_next_slot() { return 0 }
//Provides: caml_raw_backtrace_slot
//Requires: caml_invalid_argument
function caml_raw_backtrace_slot () {
  caml_invalid_argument("Printexc.get_raw_backtrace_slot: index out of bounds");
}
//Provides: caml_get_current_callstack const
function caml_get_current_callstack () { return [0]; }
//Provides: caml_sys_getenv (const)
//Requires: caml_raise_not_found
//Requires: caml_js_to_string
function caml_sys_getenv (name) {
  var g = joo_global_object;
  var n = name.toString();
  //nodejs env
  if(g.process
     && g.process.env
     && g.process.env[n] != undefined)
    return caml_js_to_string(g.process.env[n]);
  caml_raise_not_found ();
}
//Provides: caml_sys_exit
//Requires: caml_invalid_argument
function caml_sys_exit (code) {
  var g = joo_global_object;
  if(g.quit) g.quit(code);
  //nodejs
  if(g.process && g.process.exit)
    g.process.exit(code);
  caml_invalid_argument("Function 'exit' not implemented");
}

//Provides: caml_sys_get_argv const
//Requires: caml_js_to_string
//Requires: raw_array_sub
function caml_sys_get_argv () {
  var g = joo_global_object;
  var main = "a.out";
  var args = []

  if(g.process
     && g.process.argv
     && g.process.argv.length > 1) {
    var argv = g.process.argv
    //nodejs
    main = argv[1];
    args = raw_array_sub(argv,2,argv.length - 2);
  }

  var p = caml_js_to_string(main);
  var args2 = [0, p];
  for(var i = 0; i < args.length; i++)
    args2.push(caml_js_to_string(args[i]));
  return [0, p, args2];
}

//Provides: unix_inet_addr_of_string
function unix_inet_addr_of_string () {return 0;}

//Provides: caml_oo_last_id
var caml_oo_last_id = 0;

//Provides: caml_set_oo_id
//Requires: caml_oo_last_id
function caml_set_oo_id (b) {
  b[2]=caml_oo_last_id++;
  return b;
}

//Provides: caml_fresh_oo_id
//Requires: caml_oo_last_id
function caml_fresh_oo_id() {
  return caml_oo_last_id++;
}

//Provides: caml_install_signal_handler const
function caml_install_signal_handler(){return 0}


//Provides: caml_convert_raw_backtrace_slot
//Requires: caml_failwith
function caml_convert_raw_backtrace_slot(){
  caml_failwith("caml_convert_raw_backtrace_slot");
}

//Provides: caml_bswap16
function caml_bswap16(x) {
  return ((((x & 0x00FF) << 8) |
           ((x & 0xFF00) >> 8)));
}
//Provides: caml_int32_bswap
function caml_int32_bswap(x) {
  return (((x & 0x000000FF) << 24) |
          ((x & 0x0000FF00) << 8) |
          ((x & 0x00FF0000) >>> 8) |
          ((x & 0xFF000000) >>> 24));
}
//Provides: caml_int64_bswap
function caml_int64_bswap(x) {
  return [
    255,
    (((x[3] & 0x0000ff00) >> 8) |
     ((x[3] & 0x000000ff) << 8) |
     ((x[2] & 0x00ff0000))),
    (((x[2] & 0x0000ff00) >> 8) |
     ((x[2] & 0x000000ff) << 8) |
     ((x[1] & 0x00ff0000))),
    (((x[1] & 0x0000ff00) >> 8) |
     ((x[1] & 0x000000ff) << 8))]
}

//Provides: caml_list_of_js_array const (const)
function caml_list_of_js_array(a){
  var l = 0;
  for(var i=a.length - 1; i>=0; i--){
    var e = a[i];
    l = [0,e,l];
  }
  return l
}

//Provides: caml_runtime_warnings
var caml_runtime_warnings = 0;

//Provides: caml_ml_enable_runtime_warnings
//Requires: caml_runtime_warnings
function caml_ml_enable_runtime_warnings (bool) {
  caml_runtime_warnings = bool;
  return 0;
}

//Provides: caml_ml_runtime_warnings_enabled
//Requires: caml_runtime_warnings
function caml_ml_runtime_warnings_enabled (_unit) {
  return caml_runtime_warnings;
}


//Provides: caml_sys_isatty
function caml_sys_isatty(_chan) {
  return 0;
}

//Provides: caml_spacetime_enabled const (const)
function caml_spacetime_enabled(_unit) {
  return 0;
}

//Provides: caml_register_channel_for_spacetime const (const)
function caml_register_channel_for_spacetime(_channel) {
  return 0;
}

//Provides: caml_spacetime_only_works_for_native_code
//Requires: caml_failwith
function caml_spacetime_only_works_for_native_code() {
  caml_failwith("Spacetime profiling only works for native code");
}
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

//Provides: caml_int64_offset
var caml_int64_offset = Math.pow(2, -24);

//Provides: caml_int64_ucompare const
function caml_int64_ucompare(x,y) {
  if (x[3] > y[3]) return 1;
  if (x[3] < y[3]) return -1;
  if (x[2] > y[2]) return 1;
  if (x[2] < y[2]) return -1;
  if (x[1] > y[1]) return 1;
  if (x[1] < y[1]) return -1;
  return 0;
}

//Provides: caml_int64_ult const
//Requires: caml_int64_ucompare
function caml_int64_ult(x,y) { return caml_int64_ucompare(x,y) < 0; }

//Provides: caml_int64_compare const
function caml_int64_compare(x,y) {
  var x3 = x[3] << 16;
  var y3 = y[3] << 16;
  if (x3 > y3) return 1;
  if (x3 < y3) return -1;
  if (x[2] > y[2]) return 1;
  if (x[2] < y[2]) return -1;
  if (x[1] > y[1]) return 1;
  if (x[1] < y[1]) return -1;
  return 0;
}

//Provides: caml_int64_neg const
function caml_int64_neg (x) {
  var y1 = - x[1];
  var y2 = - x[2] + (y1 >> 24);
  var y3 = - x[3] + (y2 >> 24);
  return [255, y1 & 0xffffff, y2 & 0xffffff, y3 & 0xffff];
}

//Provides: caml_int64_add const
function caml_int64_add (x, y) {
  var z1 = x[1] + y[1];
  var z2 = x[2] + y[2] + (z1 >> 24);
  var z3 = x[3] + y[3] + (z2 >> 24);
  return [255, z1 & 0xffffff, z2 & 0xffffff, z3 & 0xffff];
}

//Provides: caml_int64_sub const
function caml_int64_sub (x, y) {
  var z1 = x[1] - y[1];
  var z2 = x[2] - y[2] + (z1 >> 24);
  var z3 = x[3] - y[3] + (z2 >> 24);
  return [255, z1 & 0xffffff, z2 & 0xffffff, z3 & 0xffff];
}

//Provides: caml_int64_mul const
//Requires: caml_int64_offset
function caml_int64_mul(x,y) {
  var z1 = x[1] * y[1];
  var z2 = ((z1 * caml_int64_offset) | 0) + x[2] * y[1] + x[1] * y[2];
  var z3 = ((z2 * caml_int64_offset) | 0) + x[3] * y[1] + x[2] * y[2] + x[1] * y[3];
  return [255, z1 & 0xffffff, z2 & 0xffffff, z3 & 0xffff];
}

//Provides: caml_int64_is_zero const
function caml_int64_is_zero(x) {
  return (x[3]|x[2]|x[1]) == 0;
}

//Provides: caml_int64_is_negative const
function caml_int64_is_negative(x) {
  return (x[3] << 16) < 0;
}

//Provides: caml_int64_is_min_int const
function caml_int64_is_min_int(x) {
  return x[3] == 0x8000 && (x[1]|x[2]) == 0;
}

//Provides: caml_int64_is_minus_one const
function caml_int64_is_minus_one(x) {
  return x[3] == 0xffff && (x[1]&x[2]) == 0xffffff;
}

//Provides: caml_int64_and const
function caml_int64_and (x, y) {
  return [255, x[1]&y[1], x[2]&y[2], x[3]&y[3]];
}

//Provides: caml_int64_or const
function caml_int64_or (x, y) {
  return [255, x[1]|y[1], x[2]|y[2], x[3]|y[3]];
}

//Provides: caml_int64_xor const
function caml_int64_xor (x, y) {
  return [255, x[1]^y[1], x[2]^y[2], x[3]^y[3]];
}

//Provides: caml_int64_shift_left const
function caml_int64_shift_left (x, s) {
  s = s & 63;
  if (s == 0) return x;
  if (s < 24)
    return [255,
            (x[1] << s) & 0xffffff,
            ((x[2] << s) | (x[1] >> (24 - s))) & 0xffffff,
            ((x[3] << s) | (x[2] >> (24 - s))) & 0xffff];
  if (s < 48)
    return [255, 0,
            (x[1] << (s - 24)) & 0xffffff,
            ((x[2] << (s - 24)) | (x[1] >> (48 - s))) & 0xffff];
  return [255, 0, 0, (x[1] << (s - 48)) & 0xffff];
}

//Provides: caml_int64_shift_right_unsigned const
function caml_int64_shift_right_unsigned (x, s) {
  s = s & 63;
  if (s == 0) return x;
  if (s < 24)
    return [255,
            ((x[1] >> s) | (x[2] << (24 - s))) & 0xffffff,
            ((x[2] >> s) | (x[3] << (24 - s))) & 0xffffff,
            (x[3] >> s)];
  if (s < 48)
    return [255,
            ((x[2] >> (s - 24)) | (x[3] << (48 - s))) & 0xffffff,
            (x[3] >> (s - 24)),
            0];
  return [255, (x[3] >> (s - 48)), 0, 0];
}

//Provides: caml_int64_shift_right const
function caml_int64_shift_right (x, s) {
  s = s & 63;
  if (s == 0) return x;
  var h = (x[3] << 16) >> 16;
  if (s < 24)
    return [255,
            ((x[1] >> s) | (x[2] << (24 - s))) & 0xffffff,
            ((x[2] >> s) | (h << (24 - s))) & 0xffffff,
            ((x[3] << 16) >> s) >>> 16];
  var sign = (x[3] << 16) >> 31;
  if (s < 48)
    return [255,
            ((x[2] >> (s - 24)) | (x[3] << (48 - s))) & 0xffffff,
            ((x[3] << 16) >> (s - 24) >> 16) & 0xffffff,
            sign & 0xffff];
  return [255,
          ((x[3] << 16) >> (s - 32)) & 0xffffff,
          sign & 0xffffff, sign & 0xffff];
}

//Provides: caml_int64_lsl1 const
function caml_int64_lsl1 (x) {
  x[3] = (x[3] << 1) | (x[2] >> 23);
  x[2] = ((x[2] << 1) | (x[1] >> 23)) & 0xffffff;
  x[1] = (x[1] << 1) & 0xffffff;
}

//Provides: caml_int64_lsr1 const
function caml_int64_lsr1 (x) {
  x[1] = ((x[1] >>> 1) | (x[2] << 23)) & 0xffffff;
  x[2] = ((x[2] >>> 1) | (x[3] << 23)) & 0xffffff;
  x[3] = x[3] >>> 1;
}

//Provides: caml_int64_udivmod const
//Requires: caml_int64_ucompare, caml_int64_lsl1, caml_int64_lsr1
//Requires: caml_int64_sub
//Requires: caml_obj_dup
function caml_int64_udivmod (x, y) {
  var offset = 0;
  var modulus = caml_obj_dup(x);
  var divisor = caml_obj_dup(y);
  var quotient = [255, 0, 0, 0];
  while (caml_int64_ucompare (modulus, divisor) > 0) {
    offset++;
    caml_int64_lsl1 (divisor);
  }
  while (offset >= 0) {
    offset --;
    caml_int64_lsl1 (quotient);
    if (caml_int64_ucompare (modulus, divisor) >= 0) {
      quotient[1] ++;
      modulus = caml_int64_sub (modulus, divisor);
    }
    caml_int64_lsr1 (divisor);
  }
  return [0,quotient, modulus];
}

//Provides: caml_int64_div const
//Requires: caml_int64_is_zero, caml_raise_zero_divide
//Requires: caml_int64_neg, caml_int64_udivmod
function caml_int64_div (x, y)
{
  if (caml_int64_is_zero (y)) caml_raise_zero_divide ();
  var sign = x[3] ^ y[3];
  if (x[3] & 0x8000) x = caml_int64_neg(x);
  if (y[3] & 0x8000) y = caml_int64_neg(y);
  var q = caml_int64_udivmod(x, y)[1];
  if (sign & 0x8000) q = caml_int64_neg(q);
  return q;
}

//Provides: caml_int64_mod const
//Requires: caml_int64_is_zero, caml_raise_zero_divide
//Requires: caml_int64_neg, caml_int64_udivmod
function caml_int64_mod (x, y)
{
  if (caml_int64_is_zero (y)) caml_raise_zero_divide ();
  var sign = x[3];
  if (x[3] & 0x8000) x = caml_int64_neg(x);
  if (y[3] & 0x8000) y = caml_int64_neg(y);
  var r = caml_int64_udivmod(x, y)[2];
  if (sign & 0x8000) r = caml_int64_neg(r);
  return r;
}

//Provides: caml_int64_of_int32 const
function caml_int64_of_int32 (x) {
  return [255, x & 0xffffff, (x >> 24) & 0xffffff, (x >> 31) & 0xffff]
}

//Provides: caml_int64_to_int32 const
function caml_int64_to_int32 (x) {
  return x[1] | (x[2] << 24);
}

//Provides: caml_int64_to_float const
function caml_int64_to_float (x) {
  return ((x[3] << 16) * Math.pow(2, 32) + x[2] * Math.pow(2, 24)) + x[1];
}

//Provides: caml_int64_of_float const
//Requires: caml_int64_offset
function caml_int64_of_float (x) {
  if (x < 0) x = Math.ceil(x);
  return [255,
          x & 0xffffff,
          Math.floor(x * caml_int64_offset) & 0xffffff,
          Math.floor(x * caml_int64_offset * caml_int64_offset) & 0xffff];
}

//Provides: caml_int64_format const
//Requires: caml_parse_format, caml_finish_formatting
//Requires: caml_int64_is_negative, caml_int64_neg
//Requires: caml_int64_of_int32, caml_int64_udivmod, caml_int64_to_int32
//Requires: caml_int64_is_zero, caml_str_repeat
function caml_int64_format (fmt, x) {
  var f = caml_parse_format(fmt);
  if (f.signedconv && caml_int64_is_negative(x)) {
    f.sign = -1; x = caml_int64_neg(x);
  }
  var buffer = "";
  var wbase = caml_int64_of_int32(f.base);
  var cvtbl = "0123456789abcdef";
  do {
    var p = caml_int64_udivmod(x, wbase);
    x = p[1];
    buffer = cvtbl.charAt(caml_int64_to_int32(p[2])) + buffer;
  } while (! caml_int64_is_zero(x));
  if (f.prec >= 0) {
    f.filler = ' ';
    var n = f.prec - buffer.length;
    if (n > 0) buffer = caml_str_repeat (n, '0') + buffer;
  }
  return caml_finish_formatting(f, buffer);
}

//Provides: caml_int64_of_string
//Requires: caml_parse_sign_and_base, caml_failwith, caml_parse_digit, MlString
//Requires: caml_int64_of_int32, caml_int64_udivmod, caml_int64_ult
//Requires: caml_int64_add, caml_int64_mul, caml_int64_neg
//Requires: caml_ml_string_length,caml_string_unsafe_get
function caml_int64_of_string(s) {
  var r = caml_parse_sign_and_base (s);
  var i = r[0], sign = r[1], base = r[2];
  var base64 = caml_int64_of_int32(base);
  var threshold =
    caml_int64_udivmod([255, 0xffffff, 0xfffffff, 0xffff], base64)[1];
  var c = caml_string_unsafe_get(s, i);
  var d = caml_parse_digit(c);
  if (d < 0 || d >= base) caml_failwith("int_of_string");
  var res = caml_int64_of_int32(d);
  for (;;) {
    i++;
    c = caml_string_unsafe_get(s, i);
    if (c == 95) continue;
    d = caml_parse_digit(c);
    if (d < 0 || d >= base) break;
    /* Detect overflow in multiplication base * res */
    if (caml_int64_ult(threshold, res)) caml_failwith("int_of_string");
    d = caml_int64_of_int32(d);
    res = caml_int64_add(caml_int64_mul(base64, res), d);
    /* Detect overflow in addition (base * res) + d */
    if (caml_int64_ult(res, d)) caml_failwith("int_of_string");
  }
  if (i != caml_ml_string_length(s)) caml_failwith("int_of_string");
  if (r[2] == 10 && caml_int64_ult([255, 0, 0, 0x8000], res))
    caml_failwith("int_of_string");
  if (sign < 0) res = caml_int64_neg(res);
  return res;
}

//Provides: caml_int64_of_bytes
function caml_int64_of_bytes(a) {
  return [255, a[7] | (a[6] << 8) | (a[5] << 16),
          a[4] | (a[3] << 8) | (a[2] << 16), a[1] | (a[0] << 8)];
}
//Provides: caml_int64_to_bytes
function caml_int64_to_bytes(x) {
  return [x[3] >> 8, x[3] & 0xff, x[2] >> 16, (x[2] >> 8) & 0xff, x[2] & 0xff,
          x[1] >> 16, (x[1] >> 8) & 0xff, x[1] & 0xff];
}
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2014 Jérôme Vouillon, Hugo Heuzard, Andy Ray
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
//
// Bigarray.
//
// - all bigarray types including Int64 and Complex.
// - fortran + c layouts
// - sub/slice/reshape
// - retain fast path for 1d array access
//
// Note; int64+complex support if provided by allocating a second TypedArray
// Note; accessor functions are selected when the bigarray is created.  It is assumed
//       that this results in just a function pointer and will thus be fast.

//Provides: caml_ba_init const
function caml_ba_init() {
    return 0;
}

//Provides: caml_ba_init_views
//Requires: caml_ba_views
function caml_ba_init_views() {
    if (!caml_ba_views) {
        var g = joo_global_object;
        caml_ba_views = [
            [
                g.Float32Array, g.Float64Array, g.Int8Array, g.Uint8Array,
                g.Int16Array, g.Uint16Array, g.Int32Array, g.Int32Array,
                g.Int32Array, g.Int32Array, g.Float32Array, g.Float64Array, g.Uint8Array],
            [
                0 /* General */, 0 /* General */, 0 /* General */, 0 /* General */,
                0 /* General */, 0 /* General */, 0 /* General */, 1 /* Int64 */,
                0 /* General */, 0 /* General */, 2 /* Complex */, 2 /* Complex */, 0 /* General */]
        ];
    }
}

//Provides: caml_ba_get_size
//Requires: caml_invalid_argument
function caml_ba_get_size(dims) {
    var n_dims = dims.length;
    var size = 1;
    for (var i = 0; i < n_dims; i++) {
        if (dims[i] < 0)
            caml_invalid_argument("Bigarray.create: negative dimension");
        size = size * dims[i];
    }
    return size;
}

//Provides: caml_ba_views
var caml_ba_views;

//Provides: caml_ba_create_from
//Requires: caml_ba_get_size
//Requires: caml_invalid_argument
//Requires: caml_array_bound_error
function caml_ba_create_from(data, data2, data_type, kind, layout, dims) {
    var n_dims = dims.length;
    var size = caml_ba_get_size(dims);

    //
    // Functions to compute the offsets for C or Fortran layout arrays
    // from the given array of indices.
    //
    function offset_c(index) {
        var ofs = 0;
        if (n_dims != index.length)
            caml_invalid_argument("Bigarray.get/set: bad number of dimensions");
        for (var i = 0; i < n_dims; i++) {
            if (index[i] < 0 || index[i] >= dims[i])
                caml_array_bound_error();
            ofs = (ofs * dims[i]) + index[i];
        }
        return ofs;
    }

    function offset_fortran(index) {
        var ofs = 0;
        if (n_dims != index.length)
            caml_invalid_argument("Bigarray.get/set: wrong number of indices");
        for (var i = n_dims - 1; i >= 0; i--) {
            if (index[i] < 1 || index[i] > dims[i])
                caml_array_bound_error();
            ofs = (ofs * dims[i]) + (index[i] - 1);
        }
        return ofs;
    }

    var offset = layout == 0 ? offset_c : offset_fortran;

    var dim0 = dims[0];

    //
    // Element get functions.
    //
    function get_std(index) {
        var ofs = offset(index);
        var v = data[ofs];
        return v;
    }

    function get_int64(index) {
        var off = offset(index);
        var l = data[off];
        var h = data2[off];
        return [
            255,
            l & 0xffffff,
            ((l >>> 24) & 0xff) | ((h & 0xffff) << 8),
            (h >>> 16) & 0xffff];
    }

    function get_complex(index) {
        var off = offset(index);
        var r = data[off];
        var i = data2[off];
        return [254, r, i];
    }

    var get = data_type == 1 /* Int64 */ ? get_int64 : (data_type == 2 /* Complex */ ? get_complex : get_std);

    function get1_c(i) {
        if (i < 0 || i >= dim0)
            caml_array_bound_error();
        return data[i];
    }
    function get1_fortran(i) {
        if (i < 1 || i > dim0)
            caml_array_bound_error();
        return data[i - 1];
    }
    function get1_any(i) {
        return get([i]);
    }

    var get1 = data_type == 0 /* General */ ? (layout == 0 ? get1_c : get1_fortran) : get1_any;

    //
    // Element set functions
    //
    function set_std_raw(off, v) {
        data[off] = v;
    }

    function set_int64_raw(off, v) {
        data[off] = v[1] | ((v[2] & 0xff) << 24);
        data2[off] = ((v[2] >>> 8) & 0xffff) | (v[3] << 16);
    }

    function set_complex_raw(off, v) {
        data[off] = v[1];
        data2[off] = v[2];
    }

    function set_std(index, v) {
        var ofs = offset(index);
        return set_std_raw(ofs, v);
    }
    function set_int64(index, v) {
        return set_int64_raw(offset(index), v);
    }
    function set_complex(index, v) {
        return set_complex_raw(offset(index), v);
    }

    var set = data_type == 1 /* Int64 */ ? set_int64 : (data_type == 2 /* Complex */ ? set_complex : set_std);

    function set1_c(i, v) {
        if (i < 0 || i >= dim0)
            caml_array_bound_error();
        data[i] = v;
    }
    function set1_fortran(i, v) {
        if (i < 1 || i > dim0)
            caml_array_bound_error();
        data[i - 1] = v;
    }
    function set1_any(i, v) {
        set([i], v);
    }

    var set1 = data_type == 0 /* General */ ? (layout == 0 ? set1_c : set1_fortran) : set1_any;

    //
    // other
    //
    function nth_dim(i) {
        if (i < 0 || i >= n_dims)
            caml_invalid_argument("Bigarray.dim");
        return dims[i];
    }

    function fill(v) {
        if (data_type == 0 /* General */)
            for (var i = 0; i < data.length; i++)
                set_std_raw(i, v);
        if (data_type == 1 /* Int64 */)
            for (var i = 0; i < data.length; i++)
                set_int64_raw(i, v);
        if (data_type == 2 /* Complex */)
            for (var i = 0; i < data.length; i++)
                set_complex_raw(i, v);
    }
    function blit(from) {
        if (n_dims != from.num_dims)
            caml_invalid_argument("Bigarray.blit: dimension mismatch");
        for (var i = 0; i < n_dims; i++)
            if (dims[i] != from.nth_dim(i))
                caml_invalid_argument("Bigarray.blit: dimension mismatch");
        data.set(from.data);
        if (data_type != 0 /* General */)
            data2.set(from.data2);
    }

    function sub(ofs, len) {
        var changed_dim;
        var mul = 1;

        if (layout == 0) {
            for (var i = 1; i < n_dims; i++)
                mul = mul * dims[i];
            changed_dim = 0;
        } else {
            for (var i = 0; i < (n_dims - 1); i++)
                mul = mul * dims[i];
            changed_dim = n_dims - 1;
            ofs = ofs - 1;
        }

        if (ofs < 0 || len < 0 || (ofs + len) > dims[changed_dim])
            caml_invalid_argument("Bigarray.sub: bad sub-array");

        var new_data = data.subarray(ofs * mul, (ofs + len) * mul);
        var new_data2 = data_type == 0 /* General */ ? null : data2.subarray(ofs * mul, (ofs + len) * mul);

        var new_dims = [];
        for (var i = 0; i < n_dims; i++)
            new_dims[i] = dims[i];
        new_dims[changed_dim] = len;

        return caml_ba_create_from(new_data, new_data2, data_type, kind, layout, new_dims);
    }

    function slice(vind) {
        var num_inds = vind.length;
        var index = [];
        var sub_dims = [];
        var ofs;

        if (num_inds >= n_dims)
            caml_invalid_argument("Bigarray.slice: too many indices");

        // Compute offset and check bounds
        if (layout == 0) {
            for (var i = 0; i < num_inds; i++)
                index[i] = vind[i];
            for (; i < n_dims; i++)
                index[i] = 0;
            ofs = offset(index);
            sub_dims = dims.slice(num_inds);
        } else {
            for (var i = 0; i < num_inds; i++)
                index[n_dims - num_inds + i] = vind[i];
            for (var i = 0; i < n_dims - num_inds; i++)
                index[i] = 1;
            ofs = offset(index);
            sub_dims = dims.slice(0, num_inds);
        }

        var size = caml_ba_get_size(sub_dims);
        var new_data = data.subarray(ofs, ofs + size);
        var new_data2 = data_type == 0 /* General */ ? null : data2.subarray(ofs, ofs + size);

        return caml_ba_create_from(new_data, new_data2, data_type, kind, layout, sub_dims);
    }

    function reshape(vdim) {
        var new_dim = [];
        var num_dims = vdim.length;

        if (num_dims < 1)
            caml_invalid_argument("Bigarray.reshape: bad number of dimensions");
        var num_elts = 1;
        for (var i = 0; i < num_dims; i++) {
            new_dim[i] = vdim[i];
            if (new_dim[i] < 0)
                caml_invalid_argument("Bigarray.reshape: negative dimension");
            num_elts = num_elts * new_dim[i];
        }

        // Check that sizes agree
        if (num_elts != size)
            caml_invalid_argument("Bigarray.reshape: size mismatch");

        return caml_ba_create_from(data, data2, data_type, kind, layout, new_dim);
    }

    function compare(b, total) {
        if (layout != b.layout)
            return b.layout - layout;
        if (n_dims != b.num_dims)
            return b.num_dims - n_dims;
        for (var i = 0; i < n_dims; i++)
            if (nth_dim(i) != b.nth_dim(i))
                return (nth_dim(i) < b.nth_dim(i)) ? -1 : 1;
        switch (kind) {
            case 0:
            case 1:
            case 10:
            case 11:
                var x, y;
                for (var i = 0; i < data.length; i++) {
                    x = data[i];
                    y = b.data[i];

                    //first array
                    if (x < y)
                        return -1;
                    if (x > y)
                        return 1;
                    if (x != y) {
                        if (x != y) {
                            if (!total)
                                return NaN;
                            if (x == x)
                                return 1;
                            if (y == y)
                                return -1;
                        }
                    }
                    if (data2) {
                        //second array
                        x = data2[i];
                        y = b.data2[i];
                        if (x < y)
                            return -1;
                        if (x > y)
                            return 1;
                        if (x != y) {
                            if (x != y) {
                                if (!total)
                                    return NaN;
                                if (x == x)
                                    return 1;
                                if (y == y)
                                    return -1;
                            }
                        }
                    }
                }
                ;
                break;

            case 2:
            case 3:
            case 4:
            case 5:
            case 6:
            case 8:
            case 9:
            case 12:
                for (var i = 0; i < data.length; i++) {
                    if (data[i] < b.data[i])
                        return -1;
                    if (data[i] > b.data[i])
                        return 1;
                }
                ;
                break;

            case 7:
                for (var i = 0; i < data.length; i++) {
                    if (data2[i] < b.data2[i])
                        return -1;
                    if (data2[i] > b.data2[i])
                        return 1;
                    if (data[i] < b.data[i])
                        return -1;
                    if (data[i] > b.data[i])
                        return 1;
                }
                ;
                break;
        }
        return 0;
    }

    return {
        data: data,
        data2: data2,
        data_type: data_type,
        num_dims: n_dims,
        nth_dim: nth_dim,
        kind: kind,
        layout: layout,
        size: size,
        sub: sub,
        slice: slice,
        blit: blit,
        fill: fill,
        reshape: reshape,
        get: get,
        get1: get1,
        set: set,
        set1: set1,
        compare: compare
    };
}

//Provides: caml_ba_create
//Requires: caml_ba_create_from
//Requires: caml_js_from_array
//Requires: caml_ba_views
//Requires: caml_ba_init_views
//Requires: caml_invalid_argument
//Requires: caml_ba_get_size
function caml_ba_create(kind, layout, dims_ml) {
    // Initialize TypedArray views
    caml_ba_init_views();

    // set up dimensions and calculate size
    var dims = caml_js_from_array(dims_ml);

    //var n_dims = dims.length;
    var size = caml_ba_get_size(dims);

    // Allocate TypedArray
    var view = caml_ba_views[0][kind];
    if (!view)
        caml_invalid_argument("Bigarray.create: unsupported kind");
    var data = new view(size);

    // 2nd TypedArray for int64, complex32 and complex64
    var data_type = caml_ba_views[1][kind];
    var data2 = null;
    if (data_type != 0 /* General */) {
        data2 = new view(size);
    }

    return caml_ba_create_from(data, data2, data_type, kind, layout, dims);
}

//Provides: caml_ba_kind
function caml_ba_kind(ba) {
    return ba.kind;
}

//Provides: caml_ba_layout
function caml_ba_layout(ba) {
    return ba.layout;
}

//Provides: caml_ba_num_dims
function caml_ba_num_dims(ba, _dim) {
    return ba.num_dims;
}

//Provides: caml_ba_dim
function caml_ba_dim(ba, dim) {
    return ba.nth_dim(dim);
}

//Provides: caml_ba_dim_1
function caml_ba_dim_1(ba) {
    return ba.nth_dim(0);
}

//Provides: caml_ba_dim_2
function caml_ba_dim_2(ba) {
    return ba.nth_dim(1);
}

//Provides: caml_ba_dim_3
function caml_ba_dim_3(ba) {
    return ba.nth_dim(2);
}

//Provides: caml_ba_get_generic
//Requires: caml_js_from_array
function caml_ba_get_generic(ba, index) {
    return ba.get(caml_js_from_array(index));
}

//Provides: caml_ba_uint8_get16
function caml_ba_uint8_get16(ba, i0) {
    var b1 = ba.get1(i0);
    var b2 = ba.get1(i0+1) << 8;
    return (b1 | b2);
}

//Provides: caml_ba_uint8_get32
function caml_ba_uint8_get32(ba, i0) {
    var b1 = ba.get1(i0);
    var b2 = ba.get1(i0+1) << 8;
    var b3 = ba.get1(i0+2) << 16;
    var b4 = ba.get1(i0+3) << 24;
    return (b1 | b2 | b3 | b4);
}

//Provides: caml_ba_uint8_get64
function caml_ba_uint8_get64(ba, i0) {
    var b1 = ba.get1(i0);
    var b2 = ba.get1(i0+1) << 8;
    var b3 = ba.get1(i0+2) << 16;
    var b4 = ba.get1(i0+3);
    var b5 = ba.get1(i0+4) << 8;
    var b6 = ba.get1(i0+5) << 16;
    var b7 = ba.get1(i0+6);
    var b8 = ba.get1(i0+7) << 8;
    return [255, b1 | b2 | b3, b4 | b5 | b6, b7 | b8 ];
}

//Provides: caml_ba_get_1
function caml_ba_get_1(ba, i0) {
    return ba.get1(i0);
}

//Provides: caml_ba_get_2
function caml_ba_get_2(ba, i0, i1) {
    return ba.get([i0, i1]);
}

//Provides: caml_ba_get_3
function caml_ba_get_3(ba, i0, i1, i2) {
    return ba.get([i0, i1, i2]);
}

//Provides: caml_ba_set_generic
//Requires: caml_js_from_array
function caml_ba_set_generic(ba, index, v) {
    return ba.set(caml_js_from_array(index), v);
}

//Provides: caml_ba_uint8_set16
function caml_ba_uint8_set16(ba, i0, v) {
    ba.set1(i0, v & 0xff);
    ba.set1(i0+1, (v >>> 8) & 0xff);
    return 0;
}

//Provides: caml_ba_uint8_set32
function caml_ba_uint8_set32(ba, i0, v) {
    ba.set1(i0, v & 0xff);
    ba.set1(i0+1, (v >>> 8) & 0xff);
    ba.set1(i0+2, (v >>> 16) & 0xff);
    ba.set1(i0+3, (v >>> 24) & 0xff);
    return 0;
}

//Provides: caml_ba_uint8_set64
function caml_ba_uint8_set64(ba, i0, v) {
    ba.set1(i0, v[1] & 0xff);
    ba.set1(i0+1, (v[1] >> 8) & 0xff);
    ba.set1(i0+2, v[1] >> 16);
    ba.set1(i0+3, v[2] & 0xff);
    ba.set1(i0+4, (v[2] >> 8) & 0xff);
    ba.set1(i0+5, v[2] >> 16);
    ba.set1(i0+6, v[3] & 0xff);
    ba.set1(i0+7, v[3] >> 8);
    return 0;
}

//Provides: caml_ba_set_1
function caml_ba_set_1(ba, i0, v) {
    return ba.set1(i0, v);
}

//Provides: caml_ba_set_2
function caml_ba_set_2(ba, i0, i1, v) {
    return ba.set([i0, i1], v);
}

//Provides: caml_ba_set_3
function caml_ba_set_3(ba, i0, i1, i2, v) {
    return ba.set([i0, i1, i2], v);
}

//Provides: caml_ba_blit
function caml_ba_blit(src, dst) {
    dst.blit(src);
    return 0;
}

//Provides: caml_ba_fill
function caml_ba_fill(ba, init) {
    ba.fill(init);
    return 0;
}

//Provides: caml_ba_sub
function caml_ba_sub(ba, ofs, len) {
    return ba.sub(ofs, len);
}

//Provides: caml_ba_slice
//Requires: caml_js_from_array
function caml_ba_slice(ba, vind) {
    return ba.slice(caml_js_from_array(vind));
}

//Provides: caml_ba_reshape
//Requires: caml_js_from_array
function caml_ba_reshape(ba, vind) {
    return ba.reshape(caml_js_from_array(vind));
}
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

//Provides: caml_marshal_constants
var caml_marshal_constants = {
  PREFIX_SMALL_BLOCK:         0x80,
  PREFIX_SMALL_INT:           0x40,
  PREFIX_SMALL_STRING:        0x20,
  CODE_INT8:                  0x00,
  CODE_INT16:                 0x01,
  CODE_INT32:                 0x02,
  CODE_INT64:                 0x03,
  CODE_SHARED8:               0x04,
  CODE_SHARED16:              0x05,
  CODE_SHARED32:              0x06,
  CODE_BLOCK32:               0x08,
  CODE_BLOCK64:               0x13,
  CODE_STRING8:               0x09,
  CODE_STRING32:              0x0A,
  CODE_DOUBLE_BIG:            0x0B,
  CODE_DOUBLE_LITTLE:         0x0C,
  CODE_DOUBLE_ARRAY8_BIG:     0x0D,
  CODE_DOUBLE_ARRAY8_LITTLE:  0x0E,
  CODE_DOUBLE_ARRAY32_BIG:    0x0F,
  CODE_DOUBLE_ARRAY32_LITTLE: 0x07,
  CODE_CODEPOINTER:           0x10,
  CODE_INFIXPOINTER:          0x11,
  CODE_CUSTOM:                0x12
}


//Provides: MlStringReader
//Requires: caml_new_string, caml_bytes_of_string
function MlStringReader (s, i) { this.s = caml_bytes_of_string(s); this.i = i; }
MlStringReader.prototype = {
  read8u:function () { return this.s.charCodeAt(this.i++); },
  read8s:function () { return this.s.charCodeAt(this.i++) << 24 >> 24; },
  read16u:function () {
    var s = this.s, i = this.i;
    this.i = i + 2;
    return (s.charCodeAt(i) << 8) | s.charCodeAt(i + 1)
  },
  read16s:function () {
    var s = this.s, i = this.i;
    this.i = i + 2;
    return (s.charCodeAt(i) << 24 >> 16) | s.charCodeAt(i + 1);
  },
  read32u:function () {
    var s = this.s, i = this.i;
    this.i = i + 4;
    return ((s.charCodeAt(i) << 24) | (s.charCodeAt(i+1) << 16) |
            (s.charCodeAt(i+2) << 8) | s.charCodeAt(i+3)) >>> 0;
  },
  read32s:function () {
    var s = this.s, i = this.i;
    this.i = i + 4;
    return (s.charCodeAt(i) << 24) | (s.charCodeAt(i+1) << 16) |
      (s.charCodeAt(i+2) << 8) | s.charCodeAt(i+3);
  },
  readstr:function (len) {
    var i = this.i;
    this.i = i + len;
    return caml_new_string(this.s.substring(i, i + len));
  }
}

//Provides: BigStringReader
//Requires: caml_string_of_array, caml_ba_get_1
function BigStringReader (bs, i) { this.s = bs; this.i = i; }
BigStringReader.prototype = {
  read8u:function () { return caml_ba_get_1(this.s,this.i++); },
  read8s:function () { return caml_ba_get_1(this.s,this.i++) << 24 >> 24; },
  read16u:function () {
    var s = this.s, i = this.i;
    this.i = i + 2;
    return (caml_ba_get_1(s,i) << 8) | caml_ba_get_1(s,i + 1)
  },
  read16s:function () {
    var s = this.s, i = this.i;
    this.i = i + 2;
    return (caml_ba_get_1(s,i) << 24 >> 16) | caml_ba_get_1(s,i + 1);
  },
  read32u:function () {
    var s = this.s, i = this.i;
    this.i = i + 4;
    return (caml_ba_get_1((s,i) << 24) | (caml_ba_get_1(s,i+1) << 16) |
            (caml_ba_get_1(s,i+2) << 8) | caml_ba_get_1(s,i+3)) >>> 0;
  },
  read32s:function () {
    var s = this.s, i = this.i;
    this.i = i + 4;
    return (caml_ba_get_1(s,i) << 24) | (caml_ba_get_1(s,i+1) << 16) |
      (caml_ba_get_1(s,i+2) << 8) | caml_ba_get_1(s,i+3);
  },
  readstr:function (len) {
    var i = this.i;
    var arr = new Array(len)
    for(var j = 0; j < len; j++){
      arr[j] = caml_ba_get_1(this.s, i+j);
    }
    this.i = i + len;
    return caml_string_of_array(arr);
  }
}



//Provides: caml_float_of_bytes
//Requires: caml_int64_float_of_bits, caml_int64_of_bytes
function caml_float_of_bytes (a) {
  return caml_int64_float_of_bits (caml_int64_of_bytes (a));
}

//Provides: caml_input_value_from_string mutable
//Requires: MlStringReader, caml_input_value_from_reader
function caml_input_value_from_string(s,ofs) {
  var reader = new MlStringReader (s, typeof ofs=="number"?ofs:ofs[0]);
  return caml_input_value_from_reader(reader, ofs)
}

//Provides: caml_input_value_from_reader mutable
//Requires: caml_failwith
//Requires: caml_float_of_bytes, caml_int64_of_bytes

function caml_input_value_from_reader(reader, ofs) {
  var _magic = reader.read32u ()
  var _block_len = reader.read32u ();
  var num_objects = reader.read32u ();
  var _size_32 = reader.read32u ();
  var _size_64 = reader.read32u ();
  var stack = [];
  var intern_obj_table = (num_objects > 0)?[]:null;
  var obj_counter = 0;
  function intern_rec () {
    var code = reader.read8u ();
    if (code >= 0x40 /*cst.PREFIX_SMALL_INT*/) {
      if (code >= 0x80 /*cst.PREFIX_SMALL_BLOCK*/) {
        var tag = code & 0xF;
        var size = (code >> 4) & 0x7;
        var v = [tag];
        if (size == 0) return v;
        if (intern_obj_table) intern_obj_table[obj_counter++] = v;
        stack.push(v, size);
        return v;
      } else
        return (code & 0x3F);
    } else {
      if (code >= 0x20/*cst.PREFIX_SMALL_STRING */) {
        var len = code & 0x1F;
        var v = reader.readstr (len);
        if (intern_obj_table) intern_obj_table[obj_counter++] = v;
        return v;
      } else {
        switch(code) {
        case 0x00: //cst.CODE_INT8:
          return reader.read8s ();
        case 0x01: //cst.CODE_INT16:
          return reader.read16s ();
        case 0x02: //cst.CODE_INT32:
          return reader.read32s ();
        case 0x03: //cst.CODE_INT64:
          caml_failwith("input_value: integer too large");
          break;
        case 0x04: //cst.CODE_SHARED8:
          var offset = reader.read8u ();
          return intern_obj_table[obj_counter - offset];
        case 0x05: //cst.CODE_SHARED16:
          var offset = reader.read16u ();
          return intern_obj_table[obj_counter - offset];
        case 0x06: //cst.CODE_SHARED32:
          var offset = reader.read32u ();
          return intern_obj_table[obj_counter - offset];
        case 0x08: //cst.CODE_BLOCK32:
          var header = reader.read32u ();
          var tag = header & 0xFF;
          var size = header >> 10;
          var v = [tag];
          if (size == 0) return v;
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          stack.push(v, size);
          return v;
        case 0x13: //cst.CODE_BLOCK64:
          caml_failwith ("input_value: data block too large");
          break;
        case 0x09: //cst.CODE_STRING8:
          var len = reader.read8u();
          var v = reader.readstr (len);
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          return v;
        case 0x0A: //cst.CODE_STRING32:
          var len = reader.read32u();
          var v = reader.readstr (len);
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          return v;
        case 0x0C: //cst.CODE_DOUBLE_LITTLE:
          var t = new Array(8);;
          for (var i = 0;i < 8;i++) t[7 - i] = reader.read8u ();
          var v = caml_float_of_bytes (t);
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          return v;
        case 0x0B: //cst.CODE_DOUBLE_BIG:
          var t = new Array(8);;
          for (var i = 0;i < 8;i++) t[i] = reader.read8u ();
          var v = caml_float_of_bytes (t);
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          return v;
        case 0x0E: //cst.CODE_DOUBLE_ARRAY8_LITTLE:
          var len = reader.read8u();
          var v = new Array(len+1);
          v[0] = 254;
          var t = new Array(8);;
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          for (var i = 1;i <= len;i++) {
            for (var j = 0;j < 8;j++) t[7 - j] = reader.read8u();
            v[i] = caml_float_of_bytes (t);
          }
          return v;
        case 0x0D: //cst.CODE_DOUBLE_ARRAY8_BIG:
          var len = reader.read8u();
          var v = new Array(len+1);
          v[0] = 254;
          var t = new Array(8);;
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          for (var i = 1;i <= len;i++) {
            for (var j = 0;j < 8;j++) t[j] = reader.read8u();
            v [i] = caml_float_of_bytes (t);
          }
          return v;
        case 0x07: //cst.CODE_DOUBLE_ARRAY32_LITTLE:
          var len = reader.read32u();
          var v = new Array(len+1);
          v[0] = 254;
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          var t = new Array(8);;
          for (var i = 1;i <= len;i++) {
            for (var j = 0;j < 8;j++) t[7 - j] = reader.read8u();
            v[i] = caml_float_of_bytes (t);
          }
          return v;
        case 0x0F: //cst.CODE_DOUBLE_ARRAY32_BIG:
          var len = reader.read32u();
          var v = new Array(len+1);
          v[0] = 254;
          var t = new Array(8);;
          for (var i = 1;i <= len;i++) {
            for (var j = 0;j < 8;j++) t[j] = reader.read8u();
            v [i] = caml_float_of_bytes (t);
          }
          return v;
        case 0x10: //cst.CODE_CODEPOINTER:
        case 0x11: //cst.CODE_INFIXPOINTER:
          caml_failwith ("input_value: code pointer");
          break;
        case 0x12: //cst.CODE_CUSTOM:
          var c, s = "";
          while ((c = reader.read8u ()) != 0) s += String.fromCharCode (c);
          switch(s) {
          case "_j":
            // Int64
            var t = new Array(8);;
            for (var j = 0;j < 8;j++) t[j] = reader.read8u();
            var v = caml_int64_of_bytes (t);
            if (intern_obj_table) intern_obj_table[obj_counter++] = v;
            return v;
          case "_i":
            // Int32
            var v = reader.read32s ();
            if (intern_obj_table) intern_obj_table[obj_counter++] = v;
            return v;
          case "_n":
            // Nativeint
            switch (reader.read8u ()) {
            case 1:
              var v = reader.read32s ();
              if (intern_obj_table) intern_obj_table[obj_counter++] = v;
              return v;
            case 2:
              caml_failwith("input_value: native integer value too large");
            default:
              caml_failwith("input_value: ill-formed native integer");
            }
          default:
            caml_failwith("input_value: unknown custom block identifier");
          }
        default:
          caml_failwith ("input_value: ill-formed message");
        }
      }
    }
  }
  var res = intern_rec ();
  while (stack.length > 0) {
    var size = stack.pop();
    var v = stack.pop();
    var d = v.length;
    if (d < size) stack.push(v, size);
    v[d] = intern_rec ();
  }
  if (typeof ofs!="number") ofs[0] = reader.i;
  return res;
}

//Provides: caml_marshal_data_size mutable
//Requires: caml_failwith, caml_string_unsafe_get
function caml_marshal_data_size (s, ofs) {
  function get32(s,i) {
    return (caml_string_unsafe_get(s, i) << 24) |
           (caml_string_unsafe_get(s, i + 1) << 16) |
           (caml_string_unsafe_get(s, i + 2) << 8) |
            caml_string_unsafe_get(s, i + 3);
  }
  if (get32(s, ofs) != (0x8495A6BE|0))
    caml_failwith("Marshal.data_size: bad object");
  return (get32(s, ofs + 4));
}

//Provides: caml_output_val
//Requires: caml_int64_to_bytes, caml_failwith
//Requires: caml_int64_bits_of_float
//Requires: MlString, caml_ml_string_length, caml_string_unsafe_get
var caml_output_val = function (){
  function Writer () { this.chunk = []; }
  Writer.prototype = {
    chunk_idx:20, block_len:0, obj_counter:0, size_32:0, size_64:0,
    write:function (size, value) {
      for (var i = size - 8;i >= 0;i -= 8)
        this.chunk[this.chunk_idx++] = (value >> i) & 0xFF;
    },
    write_code:function (size, code, value) {
      this.chunk[this.chunk_idx++] = code;
      for (var i = size - 8;i >= 0;i -= 8)
        this.chunk[this.chunk_idx++] = (value >> i) & 0xFF;
    },
    finalize:function () {
      this.block_len = this.chunk_idx - 20;
      this.chunk_idx = 0;
      this.write (32, 0x8495A6BE);
      this.write (32, this.block_len);
      this.write (32, this.obj_counter);
      this.write (32, this.size_32);
      this.write (32, this.size_64);
      return this.chunk;
    }
  }
  return function (v) {
    var writer = new Writer ();
    var stack = [];
    function extern_rec (v) {
      if (v instanceof Array && v[0] === (v[0]|0)) {
        if (v[0] == 255) {
          // Int64
          writer.write (8, 0x12 /*cst.CODE_CUSTOM*/);
          for (var i = 0; i < 3; i++) writer.write (8, "_j\0".charCodeAt(i));
          var b = caml_int64_to_bytes (v);
          for (var i = 0; i < 8; i++) writer.write (8, b[i]);
          writer.size_32 += 4;
          writer.size_64 += 3;
          return;
        }
        if (v[0] == 251) {
          caml_failwith("output_value: abstract value (Abstract)");
        }
        if (v[0] < 16 && v.length - 1 < 8)
          writer.write (8, 0x80 /*cst.PREFIX_SMALL_BLOCK*/ + v[0] + ((v.length - 1)<<4));
        else
          writer.write_code(32, 0x08 /*cst.CODE_BLOCK32*/, ((v.length-1) << 10) | v[0]);
        writer.size_32 += v.length;
        writer.size_64 += v.length;
        if (v.length > 1) stack.push (v, 1);
      } else if (v instanceof MlString) {
        var len = caml_ml_string_length(v);
        if (len < 0x20)
          writer.write (8, 0x20 /*cst.PREFIX_SMALL_STRING*/ + len);
        else if (len < 0x100)
          writer.write_code (8, 0x09/*cst.CODE_STRING8*/, len);
        else
          writer.write_code (32, 0x0A /*cst.CODE_STRING32*/, len);
        for (var i = 0;i < len;i++)
          writer.write (8, caml_string_unsafe_get(v,i));
        writer.size_32 += 1 + (((len + 4) / 4)|0);
        writer.size_64 += 1 + (((len + 8) / 8)|0);
      } else {
        if (v != (v|0)){
          var type_of_v = typeof v;
//
// If a float happens to be an integer it is serialized as an integer
// (Js_of_ocaml cannot tell whether the type of an integer number is
// float or integer.) This can result in unexpected crashes when
// unmarshalling using the standard runtime. It seems better to
// systematically fail on marshalling.
//
//          if(type_of_v != "number")
          caml_failwith("output_value: abstract value ("+type_of_v+")");
//          var t = caml_int64_to_bytes(caml_int64_bits_of_float(v));
//          writer.write (8, 0x0B /*cst.CODE_DOUBLE_BIG*/);
//          for(var i = 0; i<8; i++){writer.write(8,t[i])}
        }
        else if (v >= 0 && v < 0x40) {
          writer.write (8, 0X40 /*cst.PREFIX_SMALL_INT*/ + v);
        } else {
          if (v >= -(1 << 7) && v < (1 << 7))
            writer.write_code(8, 0x00 /*cst.CODE_INT8*/, v);
          else if (v >= -(1 << 15) && v < (1 << 15))
            writer.write_code(16, 0x01 /*cst.CODE_INT16*/, v);
          else
            writer.write_code(32, 0x02 /*cst.CODE_INT32*/, v);
        }
      }
    }
    extern_rec (v);
    while (stack.length > 0) {
      var i = stack.pop ();
      var v = stack.pop ();
      if (i + 1 < v.length) stack.push (v, i + 1);
      extern_rec (v[i]);
    }
    writer.finalize ();
    return writer.chunk;
  }
} ();

//Provides: caml_output_value_to_string mutable
//Requires: caml_output_val, caml_string_of_array
function caml_output_value_to_string (v, _fl) {
  /* ignores flags... */
  return caml_string_of_array (caml_output_val (v));
}

//Provides: caml_output_value_to_buffer
//Requires: caml_output_val, caml_failwith, caml_blit_string
function caml_output_value_to_buffer (s, ofs, len, v, _fl) {
  /* ignores flags... */
  var t = caml_output_val (v);
  if (t.length > len) caml_failwith ("Marshal.to_buffer: buffer overflow");
  caml_blit_string(t, 0, s, ofs, t.length);
  return 0;
}
///////// BIGSTRING
//Provides: bigstring_alloc
//Requires: caml_ba_create
function bigstring_alloc(_,size){
  return caml_ba_create(12, 0, [0,size]);
}

//Provides: bigstring_destroy_stub
function bigstring_destroy_stub(_v) {
  return 0; // noop
}

//Provides: bigstring_blit_bigstring_string_stub
//Requires: caml_string_set, caml_ba_get_1
function bigstring_blit_bigstring_string_stub(v_bstr, v_src_pos, v_str, v_dst_pos, v_len){
  for(var i = 0; i < v_len; i++){
    var c = caml_ba_get_1(v_bstr,v_src_pos + i);
    caml_string_set(v_str,v_dst_pos + i,c);
  }
  return 0;
}

//Provides: caml_blit_bigstring_to_string
//Requires: bigstring_blit_bigstring_string_stub
var caml_blit_bigstring_to_string = bigstring_blit_bigstring_string_stub

//Provides: bigstring_blit_string_bigstring_stub
//Requires: caml_string_get, caml_ba_set_1
function bigstring_blit_string_bigstring_stub(v_str, v_src_pos, v_bstr, v_dst_pos, v_len){
  for (var i = 0; i < v_len; i++) caml_ba_set_1(v_bstr,v_dst_pos + i,caml_string_get(v_str,v_src_pos + i));
  return 0;
}

//Provides: caml_blit_string_to_bigstring
//Requires: bigstring_blit_string_bigstring_stub
var caml_blit_string_to_bigstring = bigstring_blit_string_bigstring_stub

//Provides: bigstring_blit_stub
//Requires: caml_ba_get_1, caml_ba_set_1
function bigstring_blit_stub(s1, i1, s2, i2, len){
  for (var i = 0; i < len; i++) caml_ba_set_1(s2,i2 + i,caml_ba_get_1(s1,i1 + i));
  return 0;
}

//Provides: bigstring_memcmp_stub
//Requires: caml_ba_get_1
function bigstring_memcmp_stub(v_s1, v_s1_pos, v_s2, v_s2_pos, v_len){
  for (var i = 0; i < v_len; i++) {
    var a = caml_ba_get_1(v_s1,v_s1_pos + i);
    var b = caml_ba_get_1(v_s2,v_s2_pos + i);
    if (a < b) return -1;
    if (a > b) return 1;
  }
  return 0;
}

//Provides: bigstring_find
//Requires: caml_ba_get_1
function bigstring_find(bs, chr, pos, len){
  while(len > 0){
    if(caml_ba_get_1(bs,pos) == chr) return pos;
    pos++;
    len--;
  }
  return -1;
}

//Provides: bigstring_to_array_buffer mutable
function bigstring_to_array_buffer(bs) {
  return bs.data.buffer
}

//Provides: bigstring_of_array_buffer mutable
//Requires: caml_ba_create_from
function bigstring_of_array_buffer(ab) {
  var ta = new joo_global_object.Uint8Array(ab);
  return caml_ba_create_from(ta, null, 0, 12, 0, [ta.length])
}

//Provides: bigstring_marshal_data_size_stub mutable
//Requires: caml_failwith, caml_ba_uint8_get32
function bigstring_marshal_data_size_stub (s, ofs) {
  if (caml_ba_uint8_get32(s, ofs) != (0x8495A6BE|0))
    caml_failwith("Marshal.data_size: bad object");
  return (caml_ba_uint8_get32(s, ofs + 4));
}

//Provides: bigstring_unmarshal_stub mutable
//Requires: BigStringReader, caml_input_value_from_reader
function bigstring_unmarshal_stub(s,ofs) {
  var reader = new BigStringReader (s, typeof ofs=="number"?ofs:ofs[0]);
  return caml_input_value_from_reader(reader, ofs)
}


//Provides: bigstring_marshal_stub mutable
//Requires: caml_output_val, bigstring_alloc, caml_ba_set_1
function bigstring_marshal_stub (v, _fl) {
  /* ignores flags... */
  var arr = caml_output_val (v);
  var bs  = bigstring_alloc(0,arr.length);
  for(var i = 0; i < arr.length; i++){
    caml_ba_set_1(bs, i, arr[i]);
  }
  return bs;
}

//Provides: bigstring_marshal_blit_stub
//Requires: caml_output_val, caml_failwith, caml_ba_set_1
function bigstring_marshal_blit_stub (s, ofs, len, v, _fl) {
  /* ignores flags... */
  var t = caml_output_val (v);
  if (t.length > len) caml_failwith ("Marshal.to_buffer: buffer overflow");
  for(var i = 0; i < t.length; i++){
    caml_ba_set_1(s, (i + ofs), t[i]);
  }
  return t.length;
}

//Provides: caml_hash_mix_bigstring
//Requires: caml_hash_mix_string_arr
function caml_hash_mix_bigstring(h, bs) {
    return caml_hash_mix_string_arr(h,bs.data);
}
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

//Provides: jsoo_floor_log2
var log2_ok = Math.log2 && Math.log2(1.1235582092889474E+307) == 1020
function jsoo_floor_log2(x) {
    if(log2_ok) return Math.floor(Math.log2(x))
    var i = 0;
    if (x == 0) return -Infinity;
    if(x>=1) {while (x>=2) {x/=2; i++} }
    else {while (x < 1) {x*=2; i--} };
    return i;
}

//Provides: caml_int64_bits_of_float const
//Requires: jsoo_floor_log2
function caml_int64_bits_of_float (x) {
  if (!isFinite(x)) {
    if (isNaN(x)) return [255, 1, 0, 0x7ff0];
    return (x > 0)?[255,0,0,0x7ff0]:[255,0,0,0xfff0];
  }
  var sign = (x==0 && 1/x == -Infinity)?0x8000:(x>=0)?0:0x8000;
  if (sign) x = -x;
  // Int64.bits_of_float 1.1235582092889474E+307 = 0x7fb0000000000000L
  // using Math.LOG2E*Math.log(x) in place of Math.log2 result in precision lost
  var exp = jsoo_floor_log2(x) + 1023;
  if (exp <= 0) {
    exp = 0;
    x /= Math.pow(2,-1026);
  } else {
    x /= Math.pow(2,exp-1027);
    if (x < 16) {
      x *= 2; exp -=1; }
    if (exp == 0) {
      x /= 2; }
  }
  var k = Math.pow(2,24);
  var r3 = x|0;
  x = (x - r3) * k;
  var r2 = x|0;
  x = (x - r2) * k;
  var r1 = x|0;
  r3 = (r3 &0xf) | sign | exp << 4;
  return [255, r1, r2, r3];
}

//Provides: caml_int32_bits_of_float const
//Requires: jsoo_floor_log2
function caml_int32_bits_of_float (x) {
  var float32a = new joo_global_object.Float32Array(1);
  float32a[0] = x;
  var int32a = new joo_global_object.Int32Array(float32a.buffer);
  return int32a[0] | 0;
}

//FP literals can be written using the hexadecimal
//notation 0x<mantissa in hex>p<exponent> from ISO C99.
//https://github.com/dankogai/js-hexfloat/blob/master/hexfloat.js
//Provides: caml_hexstring_of_float const
//Requires: caml_js_to_string, caml_str_repeat
function caml_hexstring_of_float (x, prec, style) {
  if (!isFinite(x)) {
    if (isNaN(x)) return caml_js_to_string("nan");
    return caml_js_to_string ((x > 0)?"infinity":"-infinity");
  }
  var sign = (x==0 && 1/x == -Infinity)?1:(x>=0)?0:1;
  if(sign) x = -x;
  var exp = 0;
  if (x == 0) { }
  else if (x < 1) {
    while (x < 1 && exp > -1022)  { x *= 2; exp-- }
  } else {
    while (x >= 2) { x /= 2; exp++ }
  }
  var exp_sign = exp < 0 ? '' : '+';
  var sign_str = '';
  if (sign) sign_str = '-'
  else {
    switch(style){
    case 43 /* '+' */: sign_str = '+'; break;
    case 32 /* ' ' */: sign_str = ' '; break;
    default: break;
    }
  }
  if (prec >= 0 && prec < 13) {
    /* If a precision is given, and is small, round mantissa accordingly */
      var cst = Math.pow(2,prec * 4);
      x = Math.round(x * cst) / cst;
  }
  var x_str = x.toString(16);
  if(prec >= 0){
      var idx = x_str.indexOf('.');
    if(idx<0) {
      x_str += '.' + caml_str_repeat(prec, '0');
    }
    else {
      var size = idx+1+prec;
      if(x_str.length < size)
        x_str += caml_str_repeat(size - x_str.length, '0');
      else
        x_str = x_str.substr(0,size);
    }
  }
  return caml_js_to_string (sign_str + '0x' + x_str + 'p' + exp_sign + exp.toString(10));
}

//Provides: caml_int64_float_of_bits const
function caml_int64_float_of_bits (x) {
  var exp = (x[3] & 0x7fff) >> 4;
  if (exp == 2047) {
      if ((x[1]|x[2]|(x[3]&0xf)) == 0)
        return (x[3] & 0x8000)?(-Infinity):Infinity;
      else
        return NaN;
  }
  var k = Math.pow(2,-24);
  var res = (x[1]*k+x[2])*k+(x[3]&0xf);
  if (exp > 0) {
    res += 16;
    res *= Math.pow(2,exp-1027);
  } else
    res *= Math.pow(2,-1026);
  if (x[3] & 0x8000) res = - res;
  return res;
}

//Provides: caml_int32_float_of_bits const
function caml_int32_float_of_bits (x) {
  var int32a = new joo_global_object.Int32Array(1);
  int32a[0] = x;
  var float32a = new joo_global_object.Float32Array(int32a.buffer);
  return float32a[0];
}

//Provides: caml_classify_float const
function caml_classify_float (x) {
  if (isFinite (x)) {
    if (Math.abs(x) >= 2.2250738585072014e-308) return 0;
    if (x != 0) return 1;
    return 2;
  }
  return isNaN(x)?4:3;
}
//Provides: caml_modf_float const
function caml_modf_float (x) {
  if (isFinite (x)) {
    var neg = (1/x) < 0;
    x = Math.abs(x);
    var i = Math.floor (x);
    var f = x - i;
    if (neg) { i = -i; f = -f; }
    return [0, f, i];
  }
  if (isNaN (x)) return [0, NaN, NaN];
  return [0, 1/x, x];
}
//Provides: caml_ldexp_float const
function caml_ldexp_float (x,exp) {
  exp |= 0;
  if (exp > 1023) {
    exp -= 1023;
    x *= Math.pow(2, 1023);
    if (exp > 1023) {  // in case x is subnormal
      exp -= 1023;
      x *= Math.pow(2, 1023);
    }
  }
  if (exp < -1023) {
    exp += 1023;
    x *= Math.pow(2, -1023);
  }
  x *= Math.pow(2, exp);
  return x;
}
//Provides: caml_frexp_float const
//Requires: jsoo_floor_log2
function caml_frexp_float (x) {
  if ((x == 0) || !isFinite(x)) return [0, x, 0];
  var neg = x < 0;
  if (neg) x = - x;
  var exp = jsoo_floor_log2(x) + 1;
  x *= Math.pow(2,-exp);
  if (x < 0.5) { x *= 2; exp -= 1; }
  if (neg) x = - x;
  return [0, x, exp];
}

//Provides: caml_float_compare const
function caml_float_compare (x, y) {
  if (x === y) return 0;
  if (x < y) return -1;
  if (x > y) return 1;
  if (x === x) return 1;
  if (y === y) return -1;
  return 0;
}

//Provides: caml_copysign_float const
function caml_copysign_float (x, y) {
  if (y == 0) y = 1 / y;
  x = Math.abs(x);
  return (y < 0)?(-x):x;
}

//Provides: caml_expm1_float const
function caml_expm1_float (x) {
  var y = Math.exp(x), z = y - 1;
  return (Math.abs(x)>1?z:(z==0?x:x*z/Math.log(y)));
}

//Provides: caml_log1p_float const
function caml_log1p_float (x) {
  var y = 1 + x, z = y - 1;
  return (z==0?x:x*Math.log(y)/z);
}

//Provides: caml_hypot_float const
function caml_hypot_float (x, y) {
  var x = Math.abs(x), y = Math.abs(y);
  var a = Math.max(x, y), b = Math.min(x,y) / (a?a:1);
  return (a * Math.sqrt(1 + b*b));
}

// FIX: these five functions only give approximate results.
//Provides: caml_log10_float const
function caml_log10_float (x) { return Math.LOG10E * Math.log(x); }
//Provides: caml_cosh_float const
function caml_cosh_float (x) { return (Math.exp(x) + Math.exp(-x)) / 2; }
//Provides: caml_sinh_float const
function caml_sinh_float (x) { return (Math.exp(x) - Math.exp(-x)) / 2; }
//Provides: caml_tanh_float const
function caml_tanh_float (x) {
  var y = Math.exp(x), z = Math.exp(-x);
  return (y + z) / (y - z);
}
