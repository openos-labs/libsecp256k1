import Array "mo:base/Array";

module {
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

    public class Scalar() {
        public var n: [var Nat32] = Array.init<Nat32>(8, 0);
    };
};