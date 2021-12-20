import Array "mo:base/Array";
import Iter "mo:base/Iter";
import Nat32 "mo:base/Nat32";
import Nat64 "mo:base/Nat64";

import field "./field";
import group "./group";
import scalar "./scalar";
import Utils "./utils";
import subtle "../subtle/lib";

module {
    type Field = field.Field;
    type AffineStorage = group.AffineStorage;
    type Affine = group.Affine;
    type Jacobian = group.Jacobian;
    type Scalar = scalar.Scalar;
    type Choice = subtle.Choice;

    let AFFINE_G = group.AFFINE_G;

    let globalz_set_table_gej = group.globalz_set_table_gej;
    let set_table_gej_var = group.set_table_gej_var;

    public let WINDOW_A: Nat32 = 5;
    public let WINDOW_G: Nat32 = 16;
    public let ECMULT_TABLE_SIZE_A: Nat32 = 8; //  1 << (WINDOW_A - 2);
    public let ECMULT_TABLE_SIZE_G: Nat32 = 16384; // 1 << (WINDOW_G - 2);
    public let WNAF_BITS: Nat32 = 256;

    func odd_multiples_table_storage_var(pre: [var AffineStorage], a: Jacobian) {
        let prej: [var Jacobian] =Array.init<Jacobian>(pre.size(), group.Jacobian());
        let prea: [Affine] = Array.freeze<Affine>(Array.init<Affine>(pre.size(), group.Affine()));
        let zr: [var Field] = Array.init<Field>(pre.size(), field.Field());

        odd_multiples_table(prej, zr, a);
        set_table_gej_var(prea, Array.freeze<Jacobian>(prej), Array.freeze<Field>(zr));

        for (i in Iter.range(0, pre.size()-1)) {
            pre[i] := group.into_as(prea[i]);
        };
    };

    public func odd_multiples_table(prej: [var Jacobian], zr: [var Field], a: Jacobian) {
        let len = prej.size();
        assert(prej.size() == zr.size());
        assert(not (len == 0));
        assert(not a.is_infinity());

        let d = a.double_var(null);
        let d_ge = group.new_af(d.x, d.y);

        let a_ge = group.Affine();
        a_ge.set_gej_zinv(a, d.z);
        prej[0].x := a_ge.x;
        prej[0].y := a_ge.y;
        prej[0].z := a.z;
        prej[0].infinity := false;

        zr[0] := d.z;
        for (i in Iter.range(1, len-1)) {
            prej[i] := prej[i-1].add_ge_var(d_ge, ?zr[i]);
        };

        let l = prej[len-1].z.mul(d.z);
        prej[len-1].z := l;
    };
};