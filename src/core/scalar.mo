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

            // sumadd_fast!(l[1]);
            // muladd!(n1, SECP256K1_N_C_0);
            // muladd!(n0, SECP256K1_N_C_1);
            // m1 = extract!();
            // sumadd!(l[2]);
            // muladd!(n2, SECP256K1_N_C_0);
            // muladd!(n1, SECP256K1_N_C_1);
            // muladd!(n0, SECP256K1_N_C_2);
            // m2 = extract!();
            // sumadd!(l[3]);
            // muladd!(n3, SECP256K1_N_C_0);
            // muladd!(n2, SECP256K1_N_C_1);
            // muladd!(n1, SECP256K1_N_C_2);
            // muladd!(n0, SECP256K1_N_C_3);
            // m3 = extract!();
            // sumadd!(l[4]);
            // muladd!(n4, SECP256K1_N_C_0);
            // muladd!(n3, SECP256K1_N_C_1);
            // muladd!(n2, SECP256K1_N_C_2);
            // muladd!(n1, SECP256K1_N_C_3);
            // sumadd!(n0);
            // m4 = extract!();
            // sumadd!(l[5]);
            // muladd!(n5, SECP256K1_N_C_0);
            // muladd!(n4, SECP256K1_N_C_1);
            // muladd!(n3, SECP256K1_N_C_2);
            // muladd!(n2, SECP256K1_N_C_3);
            // sumadd!(n1);
            // m5 = extract!();
            // sumadd!(l[6]);
            // muladd!(n6, SECP256K1_N_C_0);
            // muladd!(n5, SECP256K1_N_C_1);
            // muladd!(n4, SECP256K1_N_C_2);
            // muladd!(n3, SECP256K1_N_C_3);
            // sumadd!(n2);
            // m6 = extract!();
            // sumadd!(l[7]);
            // muladd!(n7, SECP256K1_N_C_0);
            // muladd!(n6, SECP256K1_N_C_1);
            // muladd!(n5, SECP256K1_N_C_2);
            // muladd!(n4, SECP256K1_N_C_3);
            // sumadd!(n3);
            // m7 = extract!();
            // muladd!(n7, SECP256K1_N_C_1);
            // muladd!(n6, SECP256K1_N_C_2);
            // muladd!(n5, SECP256K1_N_C_3);
            // sumadd!(n4);
            // m8 = extract!();
            // muladd!(n7, SECP256K1_N_C_2);
            // muladd!(n6, SECP256K1_N_C_3);
            // sumadd!(n5);
            // m9 = extract!();
            // muladd!(n7, SECP256K1_N_C_3);
            // sumadd!(n6);
            // m10 = extract!();
            // sumadd_fast!(n7);
            // m11 = extract_fast!();
            // debug_assert!(c0 <= 1);
            // m12 = c0;

            // /* Reduce 385 bits into 258. */
            // /* p[0..8] = m[0..7] + m[8..12] * SECP256K1_N_C. */
            // c0 = m0;
            // c1 = 0;
            // c2 = 0;
            // muladd_fast!(m8, SECP256K1_N_C_0);
            // p0 = extract_fast!();
            // sumadd_fast!(m1);
            // muladd!(m9, SECP256K1_N_C_0);
            // muladd!(m8, SECP256K1_N_C_1);
            // p1 = extract!();
            // sumadd!(m2);
            // muladd!(m10, SECP256K1_N_C_0);
            // muladd!(m9, SECP256K1_N_C_1);
            // muladd!(m8, SECP256K1_N_C_2);
            // p2 = extract!();
            // sumadd!(m3);
            // muladd!(m11, SECP256K1_N_C_0);
            // muladd!(m10, SECP256K1_N_C_1);
            // muladd!(m9, SECP256K1_N_C_2);
            // muladd!(m8, SECP256K1_N_C_3);
            // p3 = extract!();
            // sumadd!(m4);
            // muladd!(m12, SECP256K1_N_C_0);
            // muladd!(m11, SECP256K1_N_C_1);
            // muladd!(m10, SECP256K1_N_C_2);
            // muladd!(m9, SECP256K1_N_C_3);
            // sumadd!(m8);
            // p4 = extract!();
            // sumadd!(m5);
            // muladd!(m12, SECP256K1_N_C_1);
            // muladd!(m11, SECP256K1_N_C_2);
            // muladd!(m10, SECP256K1_N_C_3);
            // sumadd!(m9);
            // p5 = extract!();
            // sumadd!(m6);
            // muladd!(m12, SECP256K1_N_C_2);
            // muladd!(m11, SECP256K1_N_C_3);
            // sumadd!(m10);
            // p6 = extract!();
            // sumadd_fast!(m7);
            // muladd_fast!(m12, SECP256K1_N_C_3);
            // sumadd_fast!(m11);
            // p7 = extract_fast!();
            // p8 = c0 + m12;
            // debug_assert!(p8 <= 2);

            // /* Reduce 258 bits into 256. */
            // /* r[0..7] = p[0..7] + p[8] * SECP256K1_N_C. */
            // c = u64(p0) + u64(SECP256K1_N_C_0) * u64(p8);
            // self.0[0] = u64u32(c & 0xFFFFFFFF);
            // c >>= 32;
            // c += u64(p1) + u64(SECP256K1_N_C_1) * u64(p8);
            // self.0[1] = u64u32(c & 0xFFFFFFFF);
            // c >>= 32;
            // c += u64(p2) + u64(SECP256K1_N_C_2) * u64(p8);
            // self.0[2] = u64u32(c & 0xFFFFFFFF);
            // c >>= 32;
            // c += u64(p3) + u64(SECP256K1_N_C_3) * u64(p8);
            // self.0[3] = u64u32(c & 0xFFFFFFFF);
            // c >>= 32;
            // c += u64(p4) + u64(p8);
            // self.0[4] = u64u32(c & 0xFFFFFFFF);
            // c >>= 32;
            // c += u64(p5);
            // self.0[5] = u64u32(c & 0xFFFFFFFF);
            // c >>= 32;
            // c += u64(p6);
            // self.0[6] = u64u32(c & 0xFFFFFFFF);
            // c >>= 32;
            // c += u64(p7);
            // self.0[7] = u64u32(c & 0xFFFFFFFF);
            // c >>= 32;

            // let overflow = self.check_overflow();
            // self.reduce(Choice::from(c as u8) | overflow);
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