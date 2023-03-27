pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    // log("sum_of_bits: ", sum_of_bits, " in: ", in, "eq", sum_of_bits == in);
    sum_of_bits === in;
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */
template CheckBitLength(b) {
    assert(b < 254);
    signal input in;
    signal output out;

    signal bits[b];
    var sum_of_bits = 0;

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
        sum_of_bits += (2 ** i) * bits[i];
    }

    component is_eq = IsEqual();

    is_eq.in[0] <== sum_of_bits;
    is_eq.in[1] <== in;

    out <== is_eq.out;
}

/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * else, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);

    // choose the right checks based on `is_e_zero`
    component if_else = IfThenElse();
    if_else.cond <== is_e_zero.out;
    if_else.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_else.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_else.out === 1;
}

/*
 * Right-shifts `b`-bit long `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(b, shift) {
    assert(shift < b);

    signal input x;
    signal output y;

    component x_bits = Num2Bits(b);
    x_bits.in <== x;

    signal y_bits[ b - shift ];
    for (var i = 0; i < b - shift; i++) {
        y_bits[i] <== x_bits.bits[i + shift];
    }

    component y_num = Bits2Num(b - shift);
    y_num.bits <== y_bits;
    y <== y_num.out;
}

/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    component right_shift = RightShift(P+1, round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_else[2];
    for (var i = 0; i < 2; i++) {
        if_else[i] = IfThenElse();
        if_else[i].cond <== no_overflow;
    }
    if_else[0].L <== e_out_1;
    if_else[0].R <== e_out_2;
    if_else[1].L <== m_out_1;
    if_else[1].R <== m_out_2;
    e_out <== if_else[0].out;
    m_out <== if_else[1].out;
}

/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
template LeftShift(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;

    y <-- x << shift;

    component lt = LessThan(shift_bound);
    lt.in[0] <== shift;
    lt.in[1] <== shift_bound;

    component if_else = IfThenElse();
    if_else.cond <== skip_checks;
    if_else.L <== 1;
    if_else.R <== lt.out;
    if_else.out === 1;

}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template MSNZB(b) {
    assert(b < 254);
    signal input in;
    signal input skip_checks;
    signal output one_hot[b];

    component iz = IsZero();
    iz.in <== in;

    component if_else1 = IfThenElse();
    if_else1.cond <== skip_checks;
    if_else1.L <== 0;
    if_else1.R <== iz.out;
    if_else1.out === 0;

    component if_else2 = IfThenElse();
    if_else2.cond <== skip_checks;
    if_else2.L <== 1;
    if_else2.R <== in;

    component n2b = Num2Bits(b);
    n2b.in <== if_else2.out;
    var count = 0;

    signal power_2[b];
    signal power_21[b];
    signal lt[b];
    signal gt[b];

    component and[b];
    signal sum;

    for (var i = 0 ; i < b; i++) {
        power_2[i] <== 2**i;
        power_21[i] <== 2**(i+1);
        lt[i] <-- power_2[i] <= in;
        gt[i] <-- power_21[i] > in;

        and[i] = AND();
        and[i].a <== lt[i];
        and[i].b <== gt[i];

        one_hot[i] <== and[i].out;
    }
    
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += one_hot[i];
    }

    sum <== lc;
    sum === 1 - skip_checks;
}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template Normalize(k, p, P) {
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    component is_zero = IsZero();
    is_zero.in <== m;

    component if_else = IfThenElse();
    if_else.cond <== skip_checks;
    if_else.L <== 1;
    if_else.R <== is_zero.out;
    if_else.out === 1 * skip_checks;

    component msnzb = MSNZB( P + 1 );
    msnzb.in <== m;
    msnzb.skip_checks <== skip_checks;

    var msb = 0;
    for (var i = 0; i < P + 1; i++) {
        msb = msnzb.one_hot[i] == 1 ? i : msb;
    }

    signal bit_diff <-- P - msb;
    signal bit_diff_e <-- msb - p;

    m_out <-- m << bit_diff;
    e_out <-- e + bit_diff_e;

}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.
 */
template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;

    component cwf1 = CheckWellFormedness(k, p);
    cwf1.e <== e[0];
    cwf1.m <== m[0];

    component cwf2 = CheckWellFormedness(k, p);
    cwf2.e <== e[1];
    cwf2.m <== m[1];

    signal x <-- (e[0] << (p + 1)) ;
    signal y <-- (e[1] << (p + 1)) ;

    signal mag1 <== x + m[0];
    signal mag2 <== y + m[1];

    signal dif <-- mag1 > mag2;

    signal alpha_e <-- dif ? e[0] : e[1];
    signal beta_e <-- dif ? e[1] : e[0];

    signal alpha_m <-- dif ? m[0] : m[1];
    signal beta_m <-- dif ? m[1] : m[0];

    signal diff <-- alpha_e - beta_e;

    signal greater_than <-- diff > (p + 1) ? 1 : 0;

    signal cond <-- alpha_e == 0 || greater_than;
    
    signal alpha_m2 <-- alpha_m << diff;
    signal m2 <-- alpha_m2 + beta_m;

    component normalize = Normalize(k, p, 2*p + 1);
    normalize.m <== m2;
    normalize.e <== beta_e;
    
    normalize.skip_checks <== cond;

    component round = RoundAndCheck(k, p, 2*p + 1);

    signal round_e <-- cond ? 1 : normalize.e_out ;
    signal round_m <-- cond ? 1 : normalize.m_out ;

    round.e <== round_e;
    round.m <== round_m;

    e_out <-- cond ? alpha_e : round.e_out;
    m_out <-- cond ? alpha_m : round.m_out;
}
