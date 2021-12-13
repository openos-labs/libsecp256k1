import Nat8 "mo:base/Nat8";
import Nat32 "mo:base/Nat32";
import Nat64 "mo:base/Nat64";

module {
    public func u32(a: Nat8): Nat32 {
        Nat32.fromNat(Nat8.toNat(a))
    };

    public func u8(a: Nat32): Nat8 {
        Nat8.fromNat(Nat32.toNat(a))
    };

    public func u64(a: Nat32): Nat64 {
        Nat64.fromNat(Nat32.toNat(a))
    };

    // u64 small u32
    public func u64u32(a: Nat64): Nat32 {
        Nat32.fromNat(Nat64.toNat(a));
    };

    public func u8u64(a: Nat8): Nat64 {
        Nat64.fromNat(Nat8.toNat(a))
    };

    public func boolu8(b: Bool): Nat8 {
        if b { 1 } else { 0 };
    };

    public func boolu64(b: Bool): Nat64 {
        if b { 1 } else { 0 };
    };
};