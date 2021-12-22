import Array "mo:base/Array";
import Iter "mo:base/Iter";
import Nat32 "mo:base/Nat32";
import Nat64 "mo:base/Nat64";
import Buffer "mo:base/Buffer";

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
    type JacobianStatic = group.JacobianStatic;
    type Scalar = scalar.Scalar;
    type Choice = subtle.Choice;

    let AFFINE_G = group.AFFINE_G;

    let globalz_set_table_gej = group.globalz_set_table_gej;
    let set_table_gej_var = group.set_table_gej_var;

    public let WINDOW_A: Nat = 5;
    public let WINDOW_G: Nat = 16;
    public let ECMULT_TABLE_SIZE_A: Nat = 8; //  1 << (WINDOW_A - 2);
    public let ECMULT_TABLE_SIZE_G: Nat = 16384; // 1 << (WINDOW_G - 2);
    public let WNAF_BITS: Nat = 256;

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

    /// Context for accelerating the computation of a*P + b*G.
    public class ECMultContext() {
        public let pre_g: [var AffineStorage] = Array.init<AffineStorage>(ECMULT_TABLE_SIZE_G, group.AffineStorage())

        /// Create a new `ECMultContext` from raw values.
        ///
        /// # Safety
        /// The function is unsafe because incorrect value of `pre_g` can lead to
        /// crypto logic failure. You most likely do not want to use this function,
        /// but `ECMultContext::new_boxed`.  
        //  new_from_raw()
        //  just use a.pre_g := new_value;

        /// Inspect raw values of `ECMultContext`.
        //  just use a.pre_g

        /// Generate a new `ECMultContext` on the heap. Note that this function is expensive.


    };

    /// Set a batch of group elements equal to the inputs given in jacobian
    /// coordinates. Not constant time.
    public func set_all_gej_var(a: [Jacobian]): [var Affine] {
        let az_buf = Buffer.Buffer<Field>(a.size());
        for (point in Array.vals(a)) {
            if (not point.is_infinity()) {
                az_buf.add(point.z);
            };
        };
        let az: [var Field] = az_buf.toVarArray();
        let azi: [var Field] = inv_all_var(az);

        let ret = Array.init<Affine>(a.size(), group.Affine());

        var count = 0;
        for (i in Iter.range(0, a.size()-1)) {
            ret[i].infinity := a[i].infinity;
            if (not a[i].is_infinity()) {
                ret[i].set_gej_zinv(a[i], azi[count]);
                count += 1;
            };
        };
        ret
    };

    /// Calculate the (modular) inverses of a batch of field
    /// elements. Requires the inputs' magnitudes to be at most 8. The
    /// output magnitudes are 1 (but not guaranteed to be
    /// normalized).
    public func inv_all_var(fields: [var Field]): [var Field] {
        if (fields.size() == 0) {
            return [var];
        };

        let ret_buf = Buffer.Buffer<Field>(fields.size());
        ret_buf.add(fields[0]);

        for (i in Iter.range(1, fields.size()-1)) {
            ret_buf.add(field.Field());
            ret_buf.put(i, ret_buf.get(i-1).mul(fields[i]));
        };
        let ret = ret_buf.toVarArray();

        var u = ret[fields.size() - 1].inv_var();

        for (i in Iter.range(fields.size()-1, 1)) {
            let j: Nat = i;
            let x: Nat = i - 1;
            ret[j] := ret[x].mul(u);
            u := u.mul(fields[j]);
        };

        ret[0] := u;
        ret
    };

    // Scalar.n = GEN_BLIND
    let GEN_BLIND: [Nat32] = [
        2217680822, 850875797, 1046150361, 1330484644, 4015777837, 2466086288, 2052467175, 2084507480,
    ];
    // Field::new_raw
    let GEN_INITIAL: JacobianStatic = {
        x = [
            586608, 43357028, 207667908, 262670128, 142222828, 38529388, 267186148, 45417712,
            115291924, 13447464,
        ];
        y = [
            12696548, 208302564, 112025180, 191752716, 143238548, 145482948, 228906000, 69755164,
            243572800, 210897016,
        ];
        z = [
            3685368, 75404844, 20246216, 5748944, 73206666, 107661790, 110806176, 73488774, 5707384,
            104448710,
        ];
        infinity = false;
    };

    /// Context for accelerating the computation of a*G.
    public class ECMultGenContext() {
        public var prec: [var [var AffineStorage]] = Array.init<[var AffineStorage]>(64, Array.init<AffineStorage>(16, group.AffineStorage()));
        public var blind: Scalar = scalar.Scalar();
        public var initial: Jacobian = group.Jacobian();
    };

    // public func 



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