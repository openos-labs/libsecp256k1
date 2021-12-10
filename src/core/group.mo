import Option "mo:base/Option";

import field "./field";

module {
    type Field = field.Field;
    type FieldStorage = field.FieldStorage;

    public type AffineStatic = {
        x: [Nat32];
        y: [Nat32];
        infinity: Bool;
    };

    public type JacobianStatic = {
        x: [Nat32];
        y: [Nat32];
        z: [Nat32];
        infinity: Bool;
    };

    /// A group element of the secp256k1 curve, in affine coordinates.
    public class Affine() {
        public var x: Field = field.Field();
        public var y: Field = field.Field();
        public var infinity: Bool = false;

        public func self(): Affine {
            let ret = Affine();
            ret.x := x;
            ret.y := y;
            ret.infinity := infinity;
            ret
        };

        // Default Affine()

        /// Set a group element equal to the point with given X and Y
        /// coordinates.
        // todo: maybe pointer changed later.
        public func set_xy(_x: Field, _y: Field) {
            infinity := false;
            x := _x;
            y := _y;
        };

        /// Set a group element (affine) equal to the point with the given
        /// X coordinate and a Y coordinate that is a quadratic residue
        /// modulo p. The return value is true iff a coordinate with the
        /// given X coordinate exists.
        // todo: maybe pointer changed later.
        public func set_xquad(_x: Field): Bool {
            x := _x;
            let x2 = _x.sqr();
            let x3 = _x.mul(x2);
            infinity := false;
            var c = field.Field();
            c.set_int(CURVE_B);
            c := c.add(x3);
            let (v, ret) = c.sqrt();
            y := v;
            ret
        };

        /// Set a group element (affine) equal to the point with the given
        /// X coordinate, and given oddness for Y. Return value indicates
        /// whether the result is valid.
        // todo: maybe pointer changed later.
        public func set_xo_var(x: Field, odd: Bool): Bool {
            if (not set_xquad(x)) {
                return false;
            };
            y.normalize_var();
            if (y.is_odd() != odd) {
                y := y.neg(1);
            };
            true
        };   

        /// Check whether a group element is the point at infinity.
        public func is_infinity(): Bool {
            infinity
        };

        /// Check whether a group element is valid (i.e., on the curve).
        public func is_valid_var(): Bool {
            if (is_infinity()) {
                return false;
            };
            let y2 = y.sqr();
            var x3 = x.sqr();
            x3 := x3.mul(x);
            let c = field.Field();
            c.set_int(CURVE_B);
            x3 := x3.add(c);
            x3.normalize_weak();
            y2.eq_var(x3)
        };

        public func neg_in_place(other: Affine) {
            x := other.x;
            y := other.y;
            infinity := other.infinity;

            y.normalize_weak();
            y := y.neg(1);
        };

        public func neg(): Affine {
            let ret = Affine();
            ret.neg_in_place(self());
            ret
        };

        /// Set a group element equal to another which is given in
        /// jacobian coordinates.
        public func set_gej(a: Jacobian) {
            infinity := a.infinity;
            a.z := a.z.inv();
            let z2 = a.z.sqr();
            let z3 = a.z.mul(z2);
            a.x := a.x.mul(z2);
            a.y := a.y.mul(z3);
            a.z.set_int(1);
            x := a.x;
            y := a.y;
        };

        public func from_gej(a: Jacobian): Affine {
            let ge = Affine();
            ge.set_gej(a);
            ge
        };

        public func set_gej_var(a: Jacobian) {
            infinity := a.infinity;
            if (a.is_infinity()) {
                return;
            };
            a.z := a.z.inv_var();
            let z2 = a.z.sqr();
            let z3 = a.z.mul(z2);
            a.x := a.x.mul(z2);
            a.y := a.y.mul(z3);
            a.z.set_int(1);
            x := a.x;
            y := a.y;
        };

        public func set_gej_zinv(a: Jacobian, zi: Field) {
            let zi2 = zi.sqr();
            let zi3 = zi2.mul(zi);
            x := a.x.mul(zi2);
            y := a.y.mul(zi3);
            infinity := a.infinity;
        };

        /// Clear a secp256k1_ge to prevent leaking sensitive information.
        public func clear() {
            infinity := false;
            x.clear();
            y.clear();
        };
    };

    public class Jacobian() {
        public var x: Field = field.Field();
        public var y: Field = field.Field();
        public var z: Field = field.Field();
        public var infinity: Bool = false;    

        public func self(): Jacobian {
            let ret = Jacobian();
            ret.x := x;
            ret.y := y;
            ret.z := z;
            ret.infinity := infinity;
            ret
        };

        public func assign_mut(a: Jacobian) {
            x := a.x;
            y := a.y;
            z := a.z;
            infinity := a.infinity;
        };

        /// Set a group element (jacobian) equal to the point at infinity.
        public func set_infinity() {
            infinity := true;
            x.clear();
            y.clear();
            z.clear();
        };

        /// Set a group element (jacobian) equal to another which is given
        /// in affine coordinates.
        public func set_ge(a: Affine) {
            infinity := a.infinity;
            x := a.x;
            y := a.y;
            z.set_int(1);
        };

        /// Compare the X coordinate of a group element (jacobian).
        public func eq_x_var(x: Field): Bool {
            assert(not is_infinity());
            var r = z.sqr();
            r := r.mul(x);
            let r2 = x;
            r2.normalize_weak();
            r.eq_var(r2)
        };

        /// Set r equal to the inverse of a (i.e., mirrored around the X
        /// axis).
        public func neg_in_place(a: Jacobian) {
            infinity := a.infinity;
            x := a.x;
            y := a.y;
            z := a.z;
            y.normalize_weak();
            y := y.neg(1);
        };

        public func neg(): Jacobian {
            let ret = Jacobian();
            ret.neg_in_place(self());
            ret
        };

        /// Check whether a group element is the point at infinity.
        public func is_infinity(): Bool {
            infinity
        };

        /// Check whether a group element's y coordinate is a quadratic residue.
        public func has_quad_y_var(): Bool {
            if infinity {
                return false;
            };

            let yz = y.mul(z);
            yz.is_quad_var()
        };

        /// Set r equal to the double of a. If rzr is not-NULL, r->z =
        /// a->z * *rzr (where infinity means an implicit z = 0). a may
        /// not be zero. Constant time.
        public func double_nonzero_in_place(a: Jacobian, rzr: ?Field) {
            assert(not is_infinity());
            double_var_in_place(a, rzr);
        };

        /// Set r equal to the double of a. If rzr is not-NULL, r->z =
        /// a->z * *rzr (where infinity means an implicit z = 0).
        public func double_var_in_place(a: Jacobian, rzr: ?Field) {
            infinity := a.infinity;
            if infinity {
                ignore do? {
                    rzr!.set_int(1);
                };                
                return;
            };

            ignore do? {
                field.assign(rzr!, a.y);
                rzr!.normalize_weak();
                rzr!.mul_int(2);
            };

            z := a.z.mul(a.y);
            z.mul_int(2);
            let t1 = a.x.sqr();
            t1.mul_int(3);
            var t2 = t1.sqr();
            var t3 = a.y.sqr();
            t3.mul_int(2);
            let t4 = t3.sqr();
            t4.mul_int(2);
            t3 := t3.mul(a.x);
            x := t3;
            x.mul_int(4);
            x := x.neg(4);
            x := x.add(t2);
            t2 := t2.neg(1);
            t3.mul_int(6);
            t3 := t3.add(t2);
            y := t1.mul(t3);
            t2 := t4.neg(2);
            y := y.add(t2);
        };

        public func double_var(rzr: ?Field): Jacobian {
            let ret = Jacobian();
            ret.double_var_in_place(self(), rzr);
            ret
        };

        /// Set r equal to the sum of a and b. If rzr is non-NULL, r->z =
        /// a->z * *rzr (a cannot be infinity in that case).
        public func add_var_in_place(a: Jacobian, b: Jacobian, rzr: ?Field) {
            if (a.is_infinity()) {
                assert(Option.isNull(rzr));
                assign_mut(b);
                return;
            };
            if (b.is_infinity()) {
                ignore do? {
                    rzr!.set_int(1);
                };
                assign_mut(a);
                return;
            };

            infinity := false;
            let z22 = b.z.sqr();
            let z12 = a.z.sqr();
            let u1 = a.x.mul(z22);
            let u2 = b.x.mul(z12);
            var s1 = a.y.mul(z22);
            s1 := s1.mul(b.z);
            var s2 = b.y.mul(z12);
            s2 := s2.mul(a.z);
            var h = u1.neg(1);
            h := h.add(u2);
            var i = s1.neg(1);
            i := i.add(s2);
            if (h.normalizes_to_zero_var()) {
                if (i.normalizes_to_zero_var()) {
                    double_var_in_place(a, rzr);
                } else {
                    ignore do? {
                        rzr!.set_int(0);
                    };
                    infinity := true;
                };
                return;
            };
            let i2 = i.sqr();
            let h2 = h.sqr();
            var h3 = h.add(h2);
            h := h.mul(b.z);
            ignore do? {
                rzr!.assign_mut(h);
            };
            z := a.z.mul(h);
            let t = u1.mul(h2);
            x := t;
            x.mul_int(2);
            x := x.add(h3);
            x := x.neg(3);
            x := x.add(i2);
            y := x.neg(5);
            y := y.add(t);
            y := y.mul(i);
            h3 := h3.mul(s1);
            h3 := h3.neg(1);
            y := y.add(h3);
        };

        public func add_var(b: Jacobian, rzr: ?Field): Jacobian {
            let ret = Jacobian();
            ret.add_var_in_place(self(), b, rzr);
            ret
        };

        /// Set r equal to the sum of a and b (with b given in affine
        /// coordinates, and not infinity).
        public func add_ge_in_place(a: Jacobian, b: Affine) {
            let FE1: Field = field.new(0, 0, 0, 0, 0, 0, 0, 1);

            assert(not b.infinity);

            let zz = a.z.sqr();
            let u1 = a.x;
            u1.normalize_weak();
            let u2 = b.x.mul(zz);
            let s1 = a.y;
            s1.normalize_weak();
            var s2 = b.y.mul(zz);
            s2 := s2.mul(a.z);
            var t = u1;
            t := t.add(u2);
            var m = s1;
            m := m.add(s2);
            var rr = t.sqr();
            var m_alt = u2.neg(1);
            let tt = u1.mul(m_alt);
            rr := rr.add(tt);
            let degenerate = m.normalizes_to_zero() and rr.normalizes_to_zero();
            let rr_alt = s1;
            rr_alt.mul_int(2);
            m_alt := m_alt.add(u1);

            rr_alt.cmov(rr, not degenerate);
            m_alt.cmov(m, not degenerate);

            var n = m_alt.sqr();
            var q = n.add(t);

            n := n.sqr();
            n.cmov(m, degenerate);
            t := rr_alt.sqr();
            z := a.z.mul(m_alt);
            let _infinity = do {
                let p = z.normalizes_to_zero();
                let q = a.infinity;

                switch (p, q) {
                    case (true, true) { false };
                    case (true, false) { true };
                    case (false, true) { false };
                    case (false, false) { false };
                }
            };
            z.mul_int(2);
            q := q.neg(1);
            t := t.add(q);
            t.normalize_weak();
            x := t;
            t.mul_int(2);
            t := t.add(q);
            t := t.mul(rr_alt);
            t := t.add(n);
            y := t.neg(3);
            y.normalize_weak();
            x.mul_int(4);
            y.mul_int(4);

            x.cmov(b.x, a.infinity);
            y.cmov(b.y, a.infinity);
            z.cmov(FE1, a.infinity);
            infinity := _infinity;
        };

        public func add_ge(b: Affine): Jacobian {
            let ret = Jacobian();
            ret.add_ge_in_place(self(), b);
            ret
        };

        /// Set r equal to the sum of a and b (with b given in affine
        /// coordinates). This is more efficient than
        /// secp256k1_gej_add_var. It is identical to secp256k1_gej_add_ge
        /// but without constant-time guarantee, and b is allowed to be
        /// infinity. If rzr is non-NULL, r->z = a->z * *rzr (a cannot be
        /// infinity in that case).
        public func add_ge_var_in_place(a: Jacobian, b: Affine, rzr: ?Field) {
            if (a.is_infinity()) {
                assert(Option.isNull(rzr));
                set_ge(b);
                return;
            };
            if (b.is_infinity()) {
                ignore do? {
                    rzr!.set_int(1);
                };
                assign_mut(a);
                return;
            };
            infinity := false;

            let z12 = a.z.sqr();
            let u1 = a.x;
            u1.normalize_weak();
            let u2 = b.x.mul(z12);
            let s1 = a.y;
            s1.normalize_weak();
            var s2 = b.y.mul(z12);
            s2 := s2.mul(a.z);
            var h = u1.neg(1);
            h := h.add(u2);
            var i = s1.neg(1);
            i := i.add(s2);
            if (h.normalizes_to_zero_var()) {
                if (i.normalizes_to_zero_var()) {
                    double_var_in_place(a, rzr);
                } else {
                    ignore do?{
                        rzr!.set_int(0);
                    };
                    infinity := true;
                };
                return;
            };
            let i2 = i.sqr();
            let h2 = h.sqr();
            var h3 = h.mul(h2);
            ignore do?{
                field.assign(rzr!, h);
            };
            z := a.z.mul(h);
            let t = u1.mul(h2);
            x := t;
            x.mul_int(2);
            x := x.add(h3);
            x := x.neg(3);
            x := x.add(i2);
            y := x.neg(5);
            y := y.add(t);
            y := y.mul(i);
            h3 := h3.mul(s1);
            h3 := h3.neg(1);
            y := y.add(h3);
        };

        public func add_ge_var(b: Affine, rzr: ?Field): Jacobian {
            let ret = Jacobian();
            ret.add_ge_var_in_place(self(), b, rzr);
            ret
        };


        /// Set r equal to the sum of a and b (with the inverse of b's Z
        /// coordinate passed as bzinv).
        public func add_zinv_var_in_place(a: Jacobian, b: Affine, bzinv: Field) {
            if (b.is_infinity()) {
                assign_mut(a);
                return;
            };
            if (a.is_infinity()) {
                infinity := b.infinity;
                let bzinv2 = bzinv.sqr();
                let bzinv3 = bzinv2.mul(bzinv);
                x := b.x.mul(bzinv2);
                y := b.y.mul(bzinv3);
                z.set_int(1);
                return;
            };
            infinity := false;

            let az = a.z.mul(bzinv);
            let z12 = az.sqr();
            let u1 = a.x;
            u1.normalize_weak();
            let u2 = b.x.mul(z12);
            let s1 = a.y;
            s1.normalize_weak();
            var s2 = b.y.mul(z12);
            s2 := s2.mul(az);
            var h = u1.neg(1);
            h := h.add(u2);
            var i = s1.neg(1);
            i := i.add(s2);
            if (h.normalizes_to_zero_var()) {
                if (i.normalizes_to_zero_var()) {
                    double_var_in_place(a, null);
                } else {
                    infinity := true;
                };
                return;
            };
            let i2 = i.sqr();
            let h2 = h.sqr();
            var h3 = h.mul(h2);
            z := a.z;
            z := z.mul(h);
            let t = u1.mul(h2);
            x := t;
            x.mul_int(2);
            x := x.add(h3);
            x := x.neg(3);
            x := x.add(i2);
            y := x.neg(5);
            y := y.add(t);
            y := y.mul(i);
            h3 := h3.mul(s1);
            h3 := h3.neg(1);
            y := y.add(h3);
        };

        public func add_zinv_var(b: Affine, bzinv: Field): Jacobian {
            let ret = Jacobian();
            ret.add_zinv_var_in_place(self(), b, bzinv);
            ret
        };

        /// Clear a secp256k1_gej to prevent leaking sensitive
        /// information.
        public func clear() {
            infinity := false;
            x.clear();
            y.clear();
            z.clear();
        };

        /// Rescale a jacobian point by b which must be
        /// non-zero. Constant-time.
        public func rescale(s: Field) {
            assert(not s.is_zero());
            let zz = s.sqr();
            x := x.mul(zz);
            y := y.mul(zz);
            y := y.mul(s);
            z := z.mul(s);
        };

    };

    public class AffineStorage() {
        public var x: FieldStorage = field.FieldStorage();
        public var y: FieldStorage = field.FieldStorage();

        /// If flag is true, set *r equal to *a; otherwise leave
        /// it. Constant-time.
        public func cmov(a: AffineStorage, flag: Bool) {
            x.cmov(a.x, flag);
            y.cmov(a.y, flag);
        };
    };

    public let AFFINE_INFINITY: AffineStatic = {
        x = [0, 0, 0, 0, 0, 0, 0, 0];
        y = [0, 0, 0, 0, 0, 0, 0, 0];
        infinity = true;
    };

    public let JACOBIAN_INFINITY: JacobianStatic = {
        x = [0, 0, 0, 0, 0, 0, 0, 0];
        y = [0, 0, 0, 0, 0, 0, 0, 0];
        z = [0, 0, 0, 0, 0, 0, 0, 0];
        infinity = true;
    };

    public let AFFINE_G: AffineStatic = {
        x = [0x79BE667E, 0xF9DCBBAC, 0x55A06295, 0xCE870B07, 0x029BFCDB, 0x2DCE28D9, 0x59F2815B, 0x16F81798];
        y = [0x483ADA77, 0x26A3C465, 0x5DA4FBFC, 0x0E1108A8, 0xFD17B448, 0xA6855419, 0x9C47D08F, 0xFB10D4B8];
        infinity = false;
    };

    public let CURVE_B: Nat32 = 7;

    // r will be modified
    public func set_table_gej_var(r: [Affine], a: [Jacobian], zr: [Field]) {
        assert(r.size() == a.size());

        var i: Nat = r.size() - 1;
        var zi: Field = field.Field();

        if (r.size() != 0) {
            zi := a[i].z.inv();
            r[i].set_gej_zinv(a[i], zi);

            while (i > 0) {
                zi := zi.mul(zr[i]);
                i -= 1;
                r[i].set_gej_zinv(a[i], zi);
            };
        };
    };
    
    // r, globalz will be modified
    public func globalz_set_table_gej(r: [Affine], globalz: Field, a: [Jacobian], zr: [Field]) {
        assert(r.size() == a.size() and a.size() == zr.size());

        var i: Nat = r.size() - 1;
        var zs: Field = field.Field();

        if (r.size() != 0) {
            r[i].x := a[i].x;
            r[i].y := a[i].y;
            field.assign(globalz, a[i].z);
            r[i].infinity := false;
            zs := zr[i];

            while (i > 0) {
                let temp: Nat = r.size() - 1;
                if (i != temp) {
                    zs := zs.mul(zr[i]);
                };
                i -= 1;
                r[i].set_gej_zinv(a[i], zs);
            };
        };
    };

    /// Create a new affine.
    public func new_af(x: Field, y: Field): Affine {
        let r = Affine();
        r.x := x;
        r.y := y;
        r.infinity := false;
        r
    };

    /// Create a new jacobian.
    public func new_jb(x: Field, y: Field): Jacobian {
        let r = Jacobian();
        r.x := x;
        r.y := y;
        r.infinity := false;
        r.z := field.new(0, 0, 0, 0, 0, 0, 0, 1);
        r
    };

    /// Create a new affine storage.
    public func new_as(x: FieldStorage, y: FieldStorage): AffineStorage {
        let r = AffineStorage();
        r.x := x;
        r.y := y;
        r
    };

    public func from_ge(a: Affine): Jacobian {
        let gej = Jacobian();
        gej.set_ge(a);
        gej
    };

    public func from_as(a: AffineStorage): Affine {
        new_af(a.x.from(), a.y.from())
    };

    public func into_as(a: Affine): AffineStorage {
        assert(not a.is_infinity());
        a.x.normalize();
        a.y.normalize();
        new_as(a.x.into(), a.y.into())
    };

    public func affineStatic(a: AffineStatic): Affine {
        let ret = Affine();
        ret.x.assign_mut(field.new(a.x[0], a.x[1], a.x[2], a.x[3], a.x[4], a.x[5], a.x[6], a.x[7]));
        ret.y.assign_mut(field.new(a.y[0], a.y[1], a.y[2], a.y[3], a.y[4], a.y[5], a.y[6], a.y[7]));
        ret.infinity := a.infinity;
        ret
    };

    public func jacobianStatic(a: JacobianStatic): Jacobian {
        let ret = Jacobian();
        ret.x.assign_mut(field.new(a.x[0], a.x[1], a.x[2], a.x[3], a.x[4], a.x[5], a.x[6], a.x[7]));
        ret.y.assign_mut(field.new(a.y[0], a.y[1], a.y[2], a.y[3], a.y[4], a.y[5], a.y[6], a.y[7]));
        ret.z.assign_mut(field.new(a.z[0], a.z[1], a.z[2], a.z[3], a.z[4], a.z[5], a.z[6], a.z[7]));
        ret.infinity := a.infinity;
        ret
    };


};