import Array "mo:base/Array";
import Iter "mo:base/Iter";
import Nat32 "mo:base/Nat32";
import Nat64 "mo:base/Nat64";

import Utils "./utils";
import subtle "../subtle/lib";

module {
    type Choice = subtle.Choice;

    let u8 = Utils.u8;
    let u32 = Utils.u32;
    let u64 = Utils.u64;
    let u8u64 = Utils.u8u64;
    let u64u32 = Utils.u64u32;
    let u64u8 = Utils.u64u8;
    let boolu8 = Utils.boolu8;
    let boolu32 = Utils.boolu32;
    let boolu64 = Utils.boolu64;

    let MaxU32: Nat32 = 0xffff_ffff;

    let SECP256K1_N: [Nat32] = [0xD0364141, 0xBFD25E8C, 0xAF48A03B, 0xBAAEDCE6, 0xFFFFFFFE, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF];
    let SECP256K1_N_C_0: Nat32 = 0x2FC9BEBF;
    let SECP256K1_N_C_1: Nat32 = 0x402DA173;
    let SECP256K1_N_C_2: Nat32 = 0x50B75FC4;
    let SECP256K1_N_C_3: Nat32 = 0x45512319;
    let SECP256K1_N_C_4: Nat32 = 1;

    let SECP256K1_N_H_0: Nat32 = 0x681B20A0;
    let SECP256K1_N_H_1: Nat32 = 0xDFE92F46;
    let SECP256K1_N_H_2: Nat32 = 0x57A4501D;
    let SECP256K1_N_H_3: Nat32 = 0x5D576E73;
    let SECP256K1_N_H_4: Nat32 = 0xFFFFFFFF;
    let SECP256K1_N_H_5: Nat32 = 0xFFFFFFFF;
    let SECP256K1_N_H_6: Nat32 = 0xFFFFFFFF;
    let SECP256K1_N_H_7: Nat32 = 0x7FFFFFFF;

    /// A 256-bit scalar value.
    public class Scalar() {
        public let n: [var Nat32] = Array.init<Nat32>(8, 0);

        public func self(): Scalar {
            let ret = Scalar();
            ret.n[0] := n[0];
            ret.n[1] := n[1];
            ret.n[2] := n[2];
            ret.n[3] := n[3];
            ret.n[4] := n[4];
            ret.n[5] := n[5];
            ret.n[6] := n[6];
            ret.n[7] := n[7];
            ret
        };

        /// Clear a scalar to prevent the leak of sensitive data.
        public func clear() {
            n[0] := 0;
            n[1] := 0;
            n[2] := 0;
            n[3] := 0;
            n[4] := 0;
            n[5] := 0;
            n[6] := 0;
            n[7] := 0;
        };

        /// Set a scalar to an unsigned integer.
        public func set_int(v: Nat32) {
            n[0] := v;
            n[1] := 0;
            n[2] := 0;
            n[3] := 0;
            n[4] := 0;
            n[5] := 0;
            n[6] := 0;
            n[7] := 0;
        };

        /// Access bits from a scalar. All requested bits must belong to
        /// the same 32-bit limb. can be used in wasm32
        public func bits_32(offset: Nat32, count: Nat32): Nat32 {
            let index: Nat32 = offset >> 5;
            (n[Nat32.toNat(index)] >> (offset & 0x1F)) & ((1 << count) - 1)
        };

        /// Access bits from a scalar. All requested bits must belong to
        /// the same 32-bit limb. can be used in wasm64
        public func bits_64(offset: Nat64, count: Nat64): Nat32 {
            let index: Nat64 = offset >> 5;
            u64u32((u64(n[Nat64.toNat(index)]) >> (offset & 0x1F)) & ((1 << count) - 1))
        };

        /// Access bits from a scalar. Not constant time.
        public func bits_var(offset: Nat32, count: Nat32): Nat32 {
            assert(count < 32);
            assert(offset + count <= 256);
            if ((offset + count - 1) >> 5 == offset >> 5) {
                bits_32(offset, count)
            } else {
                assert((offset >> 5) + 1 < 8);
                ((n[Nat32.toNat(offset >> 5)] >> (offset & 0x1f))
                    | (n[Nat32.toNat((offset >> 5) + 1)] << (32 - (offset & 0x1f))))
                    & ((1 << count) - 1)
            };
        };

        public func check_overflow(): Choice {
            let yes: Choice = subtle.into(0);
            let no: Choice = subtle.into(0);
            no.bitor_assign(subtle.into(boolu8(n[7] < SECP256K1_N[7]))); /* No need for a > check. */
            no.bitor_assign(subtle.into(boolu8(n[6] < SECP256K1_N[6]))); /* No need for a > check. */
            no.bitor_assign(subtle.into(boolu8(n[5] < SECP256K1_N[5]))); /* No need for a > check. */
            no.bitor_assign(subtle.into(boolu8(n[4] < SECP256K1_N[4])));
            yes.bitor_assign(subtle.into(boolu8(n[4] > SECP256K1_N[4])).bitand(no.no()));
            no.bitor_assign(subtle.into(boolu8(n[3] < SECP256K1_N[3])).bitand(yes.no()));
            yes.bitor_assign(subtle.into(boolu8(n[3] > SECP256K1_N[3])).bitand(no.no()));
            no.bitor_assign(subtle.into(boolu8(n[2] < SECP256K1_N[2])).bitand(yes.no()));
            yes.bitor_assign(subtle.into(boolu8(n[2] > SECP256K1_N[2])).bitand(no.no()));
            no.bitor_assign(subtle.into(boolu8(n[1] < SECP256K1_N[1])).bitand(yes.no()));
            yes.bitor_assign(subtle.into(boolu8(n[1] > SECP256K1_N[1])).bitand(no.no()));
            yes.bitor_assign(subtle.into(boolu8(n[0] >= SECP256K1_N[0])).bitand(no.no()));

            yes
        };

        func reduce(overflow: Choice) {
            let o = u8u64(overflow.unwrap_u8());
            var t: Nat64 = 0;

            t := u64(n[0]) + o * u64(SECP256K1_N_C_0);
            n[0] := u64u32(t & 0xFFFFFFFF);
            t >>= 32;

            t += u64(n[1]) + o * u64(SECP256K1_N_C_1);
            n[1] := u64u32(t & 0xFFFFFFFF);
            t >>= 32;

            t += u64(n[2]) + o * u64(SECP256K1_N_C_2);
            n[2] := u64u32(t & 0xFFFFFFFF);
            t >>= 32;

            t += u64(n[3]) + o * u64(SECP256K1_N_C_3);
            n[3] := u64u32(t & 0xFFFFFFFF);
            t >>= 32;

            t += u64(n[4]) + o * u64(SECP256K1_N_C_4);
            n[4] := u64u32(t & 0xFFFFFFFF);
            t >>= 32;

            t += u64(n[5]);
            n[5] := u64u32(t & 0xFFFFFFFF);
            t >>= 32;

            t += u64(n[6]);
            n[6] := u64u32(t & 0xFFFFFFFF);
            t >>= 32;

            t += u64(n[7]);
            n[7] := u64u32(t & 0xFFFFFFFF);
        };

        /// Conditionally add a power of two to a scalar. The result is
        /// not allowed to overflow.
        /// notion: bit can be motified.
        public func cadd_bit(_bit: Nat32, flag: Bool) {
            var bit: Nat32 = _bit;
            var t: Nat64 = 0;
            assert(bit < 256);
            bit += (if flag { 0 } else { MaxU32 }) & 0x100;
            t := u64(n[0]) + u64((if ((bit >> 5) == 0) { 1 } else { 0 }) << (bit & 0x1F));
            n[0] := u64u32(t & 0xFFFFFFFF);
            t >>= 32;
            t += u64(n[1]) + u64((if ((bit >> 5) == 1) { 1 } else { 0 }) << (bit & 0x1F));
            n[1] := u64u32(t & 0xFFFFFFFF);
            t >>= 32;
            t += u64(n[2]) + u64((if ((bit >> 5) == 2) { 1 } else { 0 }) << (bit & 0x1F));
            n[2] := u64u32(t & 0xFFFFFFFF);
            t >>= 32;
            t += u64(n[3]) + u64((if ((bit >> 5) == 3) { 1 } else { 0 }) << (bit & 0x1F));
            n[3] := u64u32(t & 0xFFFFFFFF);
            t >>= 32;
            t += u64(n[4]) + u64((if ((bit >> 5) == 4) { 1 } else { 0 }) << (bit & 0x1F));
            n[4] := u64u32(t & 0xFFFFFFFF);
            t >>= 32;
            t += u64(n[5]) + u64((if ((bit >> 5) == 5) { 1 } else { 0 }) << (bit & 0x1F));
            n[5] := u64u32(t & 0xFFFFFFFF);
            t >>= 32;
            t += u64(n[6]) + u64((if ((bit >> 5) == 6) { 1 } else { 0 }) << (bit & 0x1F));
            n[6] := u64u32(t & 0xFFFFFFFF);
            t >>= 32;
            t += u64(n[7]) + u64((if ((bit >> 5) == 7) { 1 } else { 0 }) << (bit & 0x1F));
            n[7] := u64u32(t & 0xFFFFFFFF);
            assert((t >> 32) == 0);
            assert(not subtle.from(self().check_overflow()));
        };

        /// Set a scalar from a big endian byte array, return whether it overflowed.
        public func set_b32(b32: [Nat8]): Choice {
            n[0] := u32(b32[31])
                | (u32(b32[30]) << 8)
                | (u32(b32[29]) << 16)
                | (u32(b32[28]) << 24);
            n[1] := u32(b32[27])
                | (u32(b32[26]) << 8)
                | (u32(b32[25]) << 16)
                | (u32(b32[24]) << 24);
            n[2] := u32(b32[23])
                | (u32(b32[22]) << 8)
                | (u32(b32[21]) << 16)
                | (u32(b32[20]) << 24);
            n[3] := u32(b32[19])
                | (u32(b32[18]) << 8)
                | (u32(b32[17]) << 16)
                | (u32(b32[16]) << 24);
            n[4] := u32(b32[15])
                | (u32(b32[14]) << 8)
                | (u32(b32[13]) << 16)
                | (u32(b32[12]) << 24);
            n[5] := u32(b32[11])
                | (u32(b32[10]) << 8)
                | (u32(b32[9]) << 16)
                | (u32(b32[8]) << 24);
            n[6] := u32(b32[7])
                | (u32(b32[6]) << 8)
                | (u32(b32[5]) << 16)
                | (u32(b32[4]) << 24);
            n[7] := u32(b32[3])
                | (u32(b32[2]) << 8)
                | (u32(b32[1]) << 16)
                | (u32(b32[0]) << 24);

            let overflow = check_overflow();
            reduce(overflow);

            overflow
        };

        /// Convert a scalar to a byte array.
        public func b32(): [var Nat8] {
            let bin = Array.init<Nat8>(32, 0);
            fill_b32(bin);
            bin
        };

        /// Convert a scalar to a byte array.
        public func fill_b32(bin: [var Nat8]) {
            bin[0] := u8(n[7] >> 24);
            bin[1] := u8(n[7] >> 16);
            bin[2] := u8(n[7] >> 8);
            bin[3] := u8(n[7]);
            bin[4] := u8(n[6] >> 24);
            bin[5] := u8(n[6] >> 16);
            bin[6] := u8(n[6] >> 8);
            bin[7] := u8(n[6]);
            bin[8] := u8(n[5] >> 24);
            bin[9] := u8(n[5] >> 16);
            bin[10] := u8(n[5] >> 8);
            bin[11] := u8(n[5]);
            bin[12] := u8(n[4] >> 24);
            bin[13] := u8(n[4] >> 16);
            bin[14] := u8(n[4] >> 8);
            bin[15] := u8(n[4]);
            bin[16] := u8(n[3] >> 24);
            bin[17] := u8(n[3] >> 16);
            bin[18] := u8(n[3] >> 8);
            bin[19] := u8(n[3]);
            bin[20] := u8(n[2] >> 24);
            bin[21] := u8(n[2] >> 16);
            bin[22] := u8(n[2] >> 8);
            bin[23] := u8(n[2]);
            bin[24] := u8(n[1] >> 24);
            bin[25] := u8(n[1] >> 16);
            bin[26] := u8(n[1] >> 8);
            bin[27] := u8(n[1]);
            bin[28] := u8(n[0] >> 24);
            bin[29] := u8(n[0] >> 16);
            bin[30] := u8(n[0] >> 8);
            bin[31] := u8(n[0]);
        };

        /// Check whether a scalar equals zero.
        public func is_zero(): Bool {
            (n[0]
                | n[1]
                | n[2]
                | n[3]
                | n[4]
                | n[5]
                | n[6]
                | n[7])
                == 0
        };

        /// Check whether a scalar equals one.
        public func is_one(): Bool {
            ((n[0] ^ 1)
                | n[1]
                | n[2]
                | n[3]
                | n[4]
                | n[5]
                | n[6]
                | n[7])
                == 0
        };

        /// Check whether a scalar is higher than the group order divided
        /// by 2.
        public func is_high(): Bool {
            let yes: Choice = subtle.into(0);
            let no: Choice = subtle.into(0);
            no.bitor_assign(subtle.into(boolu8(n[7] < SECP256K1_N_H_7)));
            yes.bitor_assign(subtle.into(boolu8(n[7] > SECP256K1_N_H_7)).bitand(no.no()));
            no.bitor_assign(subtle.into(boolu8(n[6] < SECP256K1_N_H_6)).bitand(yes.no())); /* No need for a > check. */
            no.bitor_assign(subtle.into(boolu8(n[5] < SECP256K1_N_H_5)).bitand(yes.no())); /* No need for a > check. */
            no.bitor_assign(subtle.into(boolu8(n[4] < SECP256K1_N_H_4)).bitand(yes.no())); /* No need for a > check. */
            no.bitor_assign(subtle.into(boolu8(n[3] < SECP256K1_N_H_3)).bitand(yes.no()));
            yes.bitor_assign(subtle.into(boolu8(n[3] > SECP256K1_N_H_3)).bitand(no.no()));
            no.bitor_assign(subtle.into(boolu8(n[2] < SECP256K1_N_H_2)).bitand(yes.no()));
            yes.bitor_assign(subtle.into(boolu8(n[2] > SECP256K1_N_H_2)).bitand(no.no()));
            no.bitor_assign(subtle.into(boolu8(n[1] < SECP256K1_N_H_1)).bitand(yes.no()));
            yes.bitor_assign(subtle.into(boolu8(n[1] > SECP256K1_N_H_1)).bitand(no.no()));
            yes.bitor_assign(subtle.into(boolu8(n[0] >= SECP256K1_N_H_0)).bitand(no.no()));
            
            subtle.from(yes)
        };

        /// Conditionally negate a number, in constant time.
        public func cond_neg_assign(flag: Choice) {
            let mask = MaxU32 * u32(flag.unwrap_u8());

            let nonzero = 0xFFFFFFFF * boolu64(not is_zero());
            var t = 1 * u8u64(flag.unwrap_u8());

            for (i in Iter.range(0, 7)) {
                t += u64(n[i] ^ mask) + u64(SECP256K1_N[i] & mask);
                n[i] := u64u32(t & nonzero);
                t >>= 32;
            };


            let _ = t;
        };

        func reduce_512(l: [Nat32]) {
            var c0: Nat32 = 0;
            var c1: Nat32 = 0;
            var c2: Nat32 = 0;

            var c: Nat64 = 0;
            let (n0, n1, n2, n3, n4, n5, n6, n7) =
                (l[8], l[9], l[10], l[11], l[12], l[13], l[14], l[15]);
            var m0: Nat32 = 0;
            var m1: Nat32 = 0;
            var m2: Nat32 = 0;
            var m3: Nat32 = 0;
            var m4: Nat32 = 0;            
            var m5: Nat32 = 0;
            var m6: Nat32 = 0;
            var m7: Nat32 = 0;
            var m8: Nat32 = 0;
            var m9: Nat32 = 0;
            var m10: Nat32 = 0;
            var m11: Nat32 = 0;
            var m12: Nat32 = 0;

            var p0: Nat32 = 0;
            var p1: Nat32 = 0;
            var p2: Nat32 = 0;
            var p3: Nat32 = 0;
            var p4: Nat32 = 0;
            var p5: Nat32 = 0;
            var p6: Nat32 = 0;
            var p7: Nat32 = 0;
            var p8: Nat32 = 0;

            c0 := l[0];
            c1 := 0;
            c2 := 0;
            let (ta0, ta1, ta2) = muladd_fast(c0, c1, c2, n0, SECP256K1_N_C_0);
            c0 := ta0;
            c1 := ta1;
            c2 := ta2;

            let (tb0, tb1, tb2, nm0) = extract_fast(c0, c1, c2);
            c0 := tb0;
            c1 := tb1;
            c2 := tb2;
            m0 := nm0;

            let (tc0, tc1, tc2) = muladd_fast(c0, c1, c2, n0, SECP256K1_N_C_0);
            c0 := tc0;
            c1 := tc1;
            c2 := tc2;

            let (td0, td1, td2) = sumadd_fast(c0, c1, c2, l[1]);
            c0 := td0;
            c1 := td1;
            c2 := td2;

            let (te0, te1, te2) = muladd(c0, c1, c2, n1, SECP256K1_N_C_0);
            c0 := te0;
            c1 := te1;
            c2 := te2;

            let (tf0, tf1, tf2) = muladd(c0, c1, c2, n0, SECP256K1_N_C_1);
            c0 := tf0;
            c1 := tf1;
            c2 := tf2;            

            let (tg0, tg1, tg2, nm1) = extract(c0, c1, c2);
            c0 := tg0;
            c1 := tg1;
            c2 := tg2;
            m1 := nm1;

            let (th0, th1, th2) = sumadd(c0, c1, c2, l[2]);
            c0 := th0;
            c1 := th1;
            c2 := th2;

            let (ti0, ti1, ti2) = muladd(c0, c1, c2, n2, SECP256K1_N_C_0);
            c0 := ti0;
            c1 := ti1;
            c2 := ti2;   

            let (tj0, tj1, tj2) = muladd(c0, c1, c2, n1, SECP256K1_N_C_1);
            c0 := tj0;
            c1 := tj1;
            c2 := tj2;

            let (tk0, tk1, tk2) = muladd(c0, c1, c2, n0, SECP256K1_N_C_2);
            c0 := tk0;
            c1 := tk1;
            c2 := tk2;

            let (tl0, tl1, tl2, nm2) = extract(c0, c1, c2);
            c0 := tl0;
            c1 := tl1;
            c2 := tl2;
            m2 := nm2;

            let (tm0, tm1, tm2) = sumadd(c0, c1, c2, l[3]);
            c0 := tm0;
            c1 := tm1;
            c2 := tm2;

            let (tn0, tn1, tn2) = muladd(c0, c1, c2, n3, SECP256K1_N_C_0);
            c0 := tn0;
            c1 := tn1;
            c2 := tn2;

            let (to0, to1, to2) = muladd(c0, c1, c2, n2, SECP256K1_N_C_1);
            c0 := to0;
            c1 := to1;
            c2 := to2;

            let (tp0, tp1, tp2) = muladd(c0, c1, c2, n1, SECP256K1_N_C_2);
            c0 := tp0;
            c1 := tp1;
            c2 := tp2;

            let (tq0, tq1, tq2) = muladd(c0, c1, c2, n0, SECP256K1_N_C_3);
            c0 := tq0;
            c1 := tq1;
            c2 := tq2;

            let (tr0, tr1, tr2, nm3) = extract(c0, c1, c2);
            c0 := tr0;
            c1 := tr1;
            c2 := tr2;
            m3 := nm3;

            let (ts0, ts1, ts2) = sumadd(c0, c1, c2, l[4]);
            c0 := ts0;
            c1 := ts1;
            c2 := ts2;

            let (tt0, tt1, tt2) = muladd(c0, c1, c2, n4, SECP256K1_N_C_0);
            c0 := tt0;
            c1 := tt1;
            c2 := tt2;

            let (tu0, tu1, tu2) = muladd(c0, c1, c2, n3, SECP256K1_N_C_1);
            c0 := tu0;
            c1 := tu1;
            c2 := tu2;

            let (tv0, tv1, tv2) = muladd(c0, c1, c2, n2, SECP256K1_N_C_2);
            c0 := tv0;
            c1 := tv1;
            c2 := tv2;

            let (tw0, tw1, tw2) = muladd(c0, c1, c2, n1, SECP256K1_N_C_3);
            c0 := tw0;
            c1 := tw1;
            c2 := tw2;

            let (tx0, tx1, tx2) = sumadd(c0, c1, c2, n0);
            c0 := tx0;
            c1 := tx1;
            c2 := tx2;

            let (ty0, ty1, ty2, nm4) = extract(c0, c1, c2);
            c0 := ty0;
            c1 := ty1;
            c2 := ty2;
            m4 := nm4;

            let (tz0, tz1, tz2) = sumadd(c0, c1, c2, l[5]);
            c0 := tz0;
            c1 := tz1;
            c2 := tz2;

            let (taa0, taa1, taa2) = muladd(c0, c1, c2, n5, SECP256K1_N_C_0);
            c0 := taa0;
            c1 := taa1;
            c2 := taa2;

            let (tab0, tab1, tab2) = muladd(c0, c1, c2, n4, SECP256K1_N_C_1);
            c0 := tab0;
            c1 := tab1;
            c2 := tab2;

            let (tac0, tac1, tac2) = muladd(c0, c1, c2, n3, SECP256K1_N_C_2);
            c0 := tac0;
            c1 := tac1;
            c2 := tac2;

            let (tad0, tad1, tad2) = muladd(c0, c1, c2, n2, SECP256K1_N_C_3);
            c0 := tad0;
            c1 := tad1;
            c2 := tad2;

            let (tae0, tae1, tae2) = sumadd(c0, c1, c2, n1);
            c0 := tae0;
            c1 := tae1;
            c2 := tae2;

            let (taf0, taf1, taf2, nm5) = extract(c0, c1, c2);
            c0 := taf0;
            c1 := taf1;
            c2 := taf2;
            m5 := nm5;

            let (tag0, tag1, tag2) = sumadd(c0, c1, c2, l[6]);
            c0 := tag0;
            c1 := tag1;
            c2 := tag2;

            let (tah0, tah1, tah2) = muladd(c0, c1, c2, n6, SECP256K1_N_C_0);
            c0 := tah0;
            c1 := tah1;
            c2 := tah2;

            let (tai0, tai1, tai2) = muladd(c0, c1, c2, n5, SECP256K1_N_C_1);
            c0 := tai0;
            c1 := tai1;
            c2 := tai2;

            let (taj0, taj1, taj2) = muladd(c0, c1, c2, n4, SECP256K1_N_C_2);
            c0 := taj0;
            c1 := taj1;
            c2 := taj2;

            let (tak0, tak1, tak2) = muladd(c0, c1, c2, n3, SECP256K1_N_C_3);
            c0 := tak0;
            c1 := tak1;
            c2 := tak2;

            let (tal0, tal1, tal2) = sumadd(c0, c1, c2, n2);
            c0 := tal0;
            c1 := tal1;
            c2 := tal2;
            
            let (tam0, tam1, tam2, nm6) = extract(c0, c1, c2);
            c0 := tam0;
            c1 := tam1;
            c2 := tam2;
            m6 := nm6;

            let (tan0, tan1, tan2) = sumadd(c0, c1, c2, l[7]);
            c0 := tan0;
            c1 := tan1;
            c2 := tan2;

            let (tao0, tao1, tao2) = muladd(c0, c1, c2, n7, SECP256K1_N_C_0);
            c0 := tao0;
            c1 := tao1;
            c2 := tao2;

            let (tap0, tap1, tap2) = muladd(c0, c1, c2, n6, SECP256K1_N_C_1);
            c0 := tap0;
            c1 := tap1;
            c2 := tap2;

            let (taq0, taq1, taq2) = muladd(c0, c1, c2, n5, SECP256K1_N_C_2);
            c0 := taq0;
            c1 := taq1;
            c2 := taq2;

            let (tar0, tar1, tar2) = muladd(c0, c1, c2, n4, SECP256K1_N_C_3);
            c0 := tar0;
            c1 := tar1;
            c2 := tar2;

            let (tas0, tas1, tas2) = sumadd(c0, c1, c2, n3);
            c0 := tas0;
            c1 := tas1;
            c2 := tas2;

            let (tat0, tat1, tat2, nm7) = extract(c0, c1, c2);
            c0 := tat0;
            c1 := tat1;
            c2 := tat2;
            m7 := nm7;

            let (tau0, tau1, tau2) = muladd(c0, c1, c2, n7, SECP256K1_N_C_1);
            c0 := tau0;
            c1 := tau1;
            c2 := tau2;

            let (tav0, tav1, tav2) = muladd(c0, c1, c2, n6, SECP256K1_N_C_2);
            c0 := tav0;
            c1 := tav1;
            c2 := tav2;

            let (taw0, taw1, taw2) = muladd(c0, c1, c2, n5, SECP256K1_N_C_3);
            c0 := taw0;
            c1 := taw1;
            c2 := taw2;

            let (tax0, tax1, tax2) = sumadd(c0, c1, c2, n4);
            c0 := tax0;
            c1 := tax1;
            c2 := tax2;

            let (tay0, tay1, tay2, nm8) = extract(c0, c1, c2);
            c0 := tay0;
            c1 := tay1;
            c2 := tay2;
            m8 := nm8;

            let (taz0, taz1, taz2) = muladd(c0, c1, c2, n7, SECP256K1_N_C_2);
            c0 := taz0;
            c1 := taz1;
            c2 := taz2;

            let (tba0, tba1, tba2) = muladd(c0, c1, c2, n6, SECP256K1_N_C_3);
            c0 := tba0;
            c1 := tba1;
            c2 := tba2;

            let (tbb0, tbb1, tbb2) = sumadd(c0, c1, c2, n5);
            c0 := tbb0;
            c1 := tbb1;
            c2 := tbb2;

            let (tbc0, tbc1, tbc2, nm9) = extract(c0, c1, c2);
            c0 := tbc0;
            c1 := tbc1;
            c2 := tbc2;
            m9 := nm9;

            let (tbd0, tbd1, tbd2) = muladd(c0, c1, c2, n7, SECP256K1_N_C_3);
            c0 := tbd0;
            c1 := tbd1;
            c2 := tbd2;

            let (tbe0, tbe1, tbe2) = sumadd(c0, c1, c2, n6);
            c0 := tbe0;
            c1 := tbe1;
            c2 := tbe2;
            
            let (tbf0, tbf1, tbf2, nm10) = extract(c0, c1, c2);
            c0 := tbf0;
            c1 := tbf1;
            c2 := tbf2;
            m10 := nm10;
            
            let (tbg0, tbg1, tbg2) = sumadd_fast(c0, c1, c2, n7);
            c0 := tbg0;
            c1 := tbg1;
            c2 := tbg2;


            let (tbh0, tbh1, tbh2, nm11) = extract_fast(c0, c1, c2);
            c0 := tbh0;
            c1 := tbh1;
            c2 := tbh2;
            m11 := nm11;

            assert(c0 <= 1);

            m12 := c0;

            /* Reduce 385 bits into 258. */
            /* p[0..8] = m[0..7] + m[8..12] * SECP256K1_N_C. */
            c0 := m0;
            c1 := 0;
            c2 := 0;

            let (tbi0, tbi1, tbi2) = muladd_fast(c0, c1, c2, m8, SECP256K1_N_C_0);
            c0 := tbi0;
            c1 := tbi1;
            c2 := tbi2;

            let (tbj0, tbj1, tbj2, np0) = extract_fast(c0, c1, c2);
            c0 := tbj0;
            c1 := tbj1;
            c2 := tbj2;
            p0 := np0;

            let (tbk0, tbk1, tbk2) = sumadd_fast(c0, c1, c2, m1);
            c0 := tbk0;
            c1 := tbk1;
            c2 := tbk2;

            let (tbl0, tbl1, tbl2) = muladd(c0, c1, c2, m9, SECP256K1_N_C_0);
            c0 := tbl0;
            c1 := tbl1;
            c2 := tbl2;

            let (tbm0, tbm1, tbm2) = muladd(c0, c1, c2, m8, SECP256K1_N_C_1);
            c0 := tbm0;
            c1 := tbm1;
            c2 := tbm2;

            let (tbn0, tbn1, tbn2, np1) = extract(c0, c1, c2);
            c0 := tbn0;
            c1 := tbn1;
            c2 := tbn2;
            p1 := np1;

            let (tbo0, tbo1, tbo2) = sumadd(c0, c1, c2, m2);
            c0 := tbo0;
            c1 := tbo1;
            c2 := tbo2;

            let (tbp0, tbp1, tbp2) = muladd(c0, c1, c2, m10, SECP256K1_N_C_0);
            c0 := tbp0;
            c1 := tbp1;
            c2 := tbp2;
          
            let (tbq0, tbq1, tbq2) = muladd(c0, c1, c2, m9, SECP256K1_N_C_1);
            c0 := tbq0;
            c1 := tbq1;
            c2 := tbq2;

            let (tbr0, tbr1, tbr2) = muladd(c0, c1, c2, m8, SECP256K1_N_C_2);
            c0 := tbr0;
            c1 := tbr1;
            c2 := tbr2;

            let (tbs0, tbs1, tbs2, np2) = extract(c0, c1, c2);
            c0 := tbs0;
            c1 := tbs1;
            c2 := tbs2;
            p2 := np2;

            let (tbt0, tbt1, tbt2) = sumadd(c0, c1, c2, m3);
            c0 := tbt0;
            c1 := tbt1;
            c2 := tbt2;

            let (tbu0, tbu1, tbu2) = muladd(c0, c1, c2, m11, SECP256K1_N_C_0);
            c0 := tbu0;
            c1 := tbu1;
            c2 := tbu2;

            let (tbv0, tbv1, tbv2) = muladd(c0, c1, c2, m10, SECP256K1_N_C_1);
            c0 := tbv0;
            c1 := tbv1;
            c2 := tbv2;

            let (tbw0, tbw1, tbw2) = muladd(c0, c1, c2, m9, SECP256K1_N_C_2);
            c0 := tbw0;
            c1 := tbw1;
            c2 := tbw2;

            let (tbx0, tbx1, tbx2) = muladd(c0, c1, c2, m8, SECP256K1_N_C_3);
            c0 := tbx0;
            c1 := tbx1;
            c2 := tbx2;

            let (tby0, tby1, tby2, np3) = extract(c0, c1, c2);
            c0 := tby0;
            c1 := tby1;
            c2 := tby2;
            p3 := np3;

            let (tbz0, tbz1, tbz2) = sumadd(c0, c1, c2, m4);
            c0 := tbz0;
            c1 := tbz1;
            c2 := tbz2;

            let (tca0, tca1, tca2) = muladd(c0, c1, c2, m12, SECP256K1_N_C_0);
            c0 := tca0;
            c1 := tca1;
            c2 := tca2;

            let (tcb0, tcb1, tcb2) = muladd(c0, c1, c2, m11, SECP256K1_N_C_1);
            c0 := tcb0;
            c1 := tcb1;
            c2 := tcb2;

            let (tcc0, tcc1, tcc2) = muladd(c0, c1, c2, m10, SECP256K1_N_C_2);
            c0 := tcc0;
            c1 := tcc1;
            c2 := tcc2;

            let (tcd0, tcd1, tcd2) = muladd(c0, c1, c2, m9, SECP256K1_N_C_3);
            c0 := tcd0;
            c1 := tcd1;
            c2 := tcd2;

            let (tce0, tce1, tce2) = sumadd(c0, c1, c2, m8);
            c0 := tce0;
            c1 := tce1;
            c2 := tce2;

            let (tcf0, tcf1, tcf2, np4) = extract(c0, c1, c2);
            c0 := tcf0;
            c1 := tcf1;
            c2 := tcf2;
            p4 := np4;

            let (tcg0, tcg1, tcg2) = sumadd(c0, c1, c2, m5);
            c0 := tcg0;
            c1 := tcg1;
            c2 := tcg2;

            let (tch0, tch1, tch2) = muladd(c0, c1, c2, m12, SECP256K1_N_C_1);
            c0 := tch0;
            c1 := tch1;
            c2 := tch2;

            let (tci0, tci1, tci2) = muladd(c0, c1, c2, m11, SECP256K1_N_C_2);
            c0 := tci0;
            c1 := tci1;
            c2 := tci2;

            let (tcj0, tcj1, tcj2) = muladd(c0, c1, c2, m10, SECP256K1_N_C_3);
            c0 := tcj0;
            c1 := tcj1;
            c2 := tcj2;

            let (tck0, tck1, tck2) = sumadd(c0, c1, c2, m9);
            c0 := tck0;
            c1 := tck1;
            c2 := tck2;

            let (tcl0, tcl1, tcl2, np5) = extract(c0, c1, c2);
            c0 := tcl0;
            c1 := tcl1;
            c2 := tcl2;
            p5 := np5;

            let (tcm0, tcm1, tcm2) = sumadd(c0, c1, c2, m6);
            c0 := tcm0;
            c1 := tcm1;
            c2 := tcm2;

            let (tcn0, tcn1, tcn2) = muladd(c0, c1, c2, m12, SECP256K1_N_C_2);
            c0 := tcn0;
            c1 := tcn1;
            c2 := tcn2;

            let (tco0, tco1, tco2) = muladd(c0, c1, c2, m11, SECP256K1_N_C_3);
            c0 := tco0;
            c1 := tco1;
            c2 := tco2;

            let (tcp0, tcp1, tcp2) = sumadd(c0, c1, c2, m10);
            c0 := tcp0;
            c1 := tcp1;
            c2 := tcp2;

            let (tcq0, tcq1, tcq2, np6) = extract(c0, c1, c2);
            c0 := tcq0;
            c1 := tcq1;
            c2 := tcq2;
            p6 := np6;

            let (tcr0, tcr1, tcr2) = sumadd_fast(c0, c1, c2, m7);
            c0 := tcr0;
            c1 := tcr1;
            c2 := tcr2;

            let (tcs0, tcs1, tcs2) = muladd_fast(c0, c1, c2, m12, SECP256K1_N_C_3);
            c0 := tcs0;
            c1 := tcs1;
            c2 := tcs2;

            let (tct0, tct1, tct2) = sumadd_fast(c0, c1, c2, m11);
            c0 := tct0;
            c1 := tct1;
            c2 := tct2;

            let (tcu0, tcu1, tcu2, np7) = extract_fast(c0, c1, c2);
            c0 := tcu0;
            c1 := tcu1;
            c2 := tcu2;
            p7 := np7;

            p8 := c0 + m12;


            assert(p8 <= 2);

            

            /* Reduce 258 bits into 256. */
            /* r[0..7] = p[0..7] + p[8] * SECP256K1_N_C. */
            c := u64(p0) + u64(SECP256K1_N_C_0) * u64(p8);
            n[0] := u64u32(c & 0xFFFFFFFF);
            c >>= 32;
            c += u64(p1) + u64(SECP256K1_N_C_1) * u64(p8);
            n[1] := u64u32(c & 0xFFFFFFFF);
            c >>= 32;
            c += u64(p2) + u64(SECP256K1_N_C_2) * u64(p8);
            n[2] := u64u32(c & 0xFFFFFFFF);
            c >>= 32;
            c += u64(p3) + u64(SECP256K1_N_C_3) * u64(p8);
            n[3] := u64u32(c & 0xFFFFFFFF);
            c >>= 32;
            c += u64(p4) + u64(p8);
            n[4] := u64u32(c & 0xFFFFFFFF);
            c >>= 32;
            c += u64(p5);
            n[5] := u64u32(c & 0xFFFFFFFF);
            c >>= 32;
            c += u64(p6);
            n[6] := u64u32(c & 0xFFFFFFFF);
            c >>= 32;
            c += u64(p7);
            n[7] := u64u32(c & 0xFFFFFFFF);
            c >>= 32;

            let overflow = check_overflow();
            reduce(subtle.into(u64u8(c)).bitor(overflow));
        };

    };

    public func muladd(c0: Nat32, c1: Nat32, c2: Nat32, a: Nat32, b: Nat32): (Nat32, Nat32, Nat32) {
        var c3 = c0;
        var c4 = c1;
        var c5 = c2;

        let t = u64(a) * u64(b);
        var th: Nat32 = u64u32(t >> 32);
        let tl = u64u32(t);
        c3 := Nat32.addWrap(c3, tl);
        th := Nat32.addWrap(th, Utils.boolu32(c3 < tl));
        c4 := Nat32.addWrap(c4, th);
        c5 := Nat32.addWrap(c5, Utils.boolu32(c4 < th));
        assert(c4 >= th or c5 != 0);
        (c3, c4, c5)
    };

    public func muladd_fast(c0: Nat32, c1: Nat32, c2: Nat32, a: Nat32, b: Nat32): (Nat32, Nat32, Nat32) {
        var c3 = c0;
        var c4 = c1;
        var c5 = c2;

        let t = u64(a) * u64(b);
        var th: Nat32 = u64u32(t >> 32);
        let tl = u64u32(t);
        c3 := Nat32.addWrap(c3, tl);
        th := Nat32.addWrap(th, Utils.boolu32(c3 < tl));
        c4 := Nat32.addWrap(c4, th);
        assert(c4 >= th);
        (c3, c4, c5)
    };

    public func muladd2(c0: Nat32, c1: Nat32, c2: Nat32, a: Nat32, b: Nat32): (Nat32, Nat32, Nat32) {
        var c3 = c0;
        var c4 = c1;
        var c5 = c2;

        let t = u64(a) * u64(b);
        let th: Nat32 = u64u32(t >> 32);
        let tl = u64u32(t);
        var th2 = Nat32.addWrap(th, th);
        c5 := Nat32.addWrap(c5, Utils.boolu32(th2 < th));
        assert(th2 >= th or c5 != 0);
        let tl2 = Nat32.addWrap(tl, tl);
        th2 := Nat32.addWrap(th2, Utils.boolu32(tl2 < tl));
        c3 := Nat32.addWrap(c3, tl2);
        th2 := Nat32.addWrap(th2, Utils.boolu32(c3 < tl2));
        c5 := Nat32.addWrap(c5, Utils.boolu32(c3 < tl2 and th2 == 0 ));
        assert(c3 >= tl2 or th2 != 0 or c5 != 0);

        c4 := Nat32.addWrap(c4, th2);
        c5 := Nat32.addWrap(c5, Utils.boolu32(c4 < th2));
        assert(c4 >= th2 or c5 != 0);
        (c3, c4, c5)
    };


    public func sumadd(c0: Nat32, c1: Nat32, c2: Nat32, a: Nat32): (Nat32, Nat32, Nat32) {
        var c3 = c0;
        var c4 = c1;
        var c5 = c2;

        c3 := Nat32.addWrap(c3, a);
        let over = Utils.boolu32(c3 < a);
        c4 := Nat32.addWrap(c4, over);
        c5 := Nat32.addWrap(c5, Utils.boolu32(c4 < over));
        (c3, c4, c5)
    };

    public func sumadd_fast(c0: Nat32, c1: Nat32, c2: Nat32, a: Nat32): (Nat32, Nat32, Nat32) {
        var c3 = c0;
        var c4 = c1;
        var c5 = c2;

        c3 := Nat32.addWrap(c3, a);
        c4 := Nat32.addWrap(c4, Utils.boolu32(c3 < a));
        assert(c4 != 0 or c3 >= a);
        assert(c5 == 0);
        (c3, c4, c5)
    };

    public func extract(c0: Nat32, c1: Nat32, c2: Nat32): (Nat32, Nat32, Nat32, Nat32) {
        let n = c0;
        let ta0 = c1;
        let ta1 = c2;
        let ta2: Nat32 = 0;
        (ta0, ta1, ta2, n)
    };

    public func extract_fast(c0: Nat32, c1: Nat32, c2: Nat32): (Nat32, Nat32, Nat32, Nat32) {
        let n = c0;
        let ta0 = c1;
        let ta1: Nat32 = 0;
        assert(c2 == 0);
        (ta0, ta1, c2, n)
    };

    

    /// Create a scalar from an unsigned integer.
    public func from_int(v: Nat32): Scalar {
        let ret = Scalar();
        ret.set_int(v);
        ret
    };


};