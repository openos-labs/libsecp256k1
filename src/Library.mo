/// libsecp256k1
///
/// Pure Rust implementation of the secp256k1 curve and fast ECDSA
/// signatures. The secp256k1 curve is used extensively in Bitcoin and
/// Ethereum-alike cryptocurrencies.

import Array "mo:base/Array";
import Iter "mo:base/Iter";
import Text "mo:base/Text";

module {
  // I'm a private function that's not exposed to consumers of this library
  func reverseText(t : Text) : Text {
    let chars : [Char] = Iter.toArray(Text.toIter(t));
    let size = chars.size();
    let reversedChars = Array.tabulate(size, func (i : Nat) : Char {
      chars[size - i - 1]
    });
    Text.fromIter(Iter.fromArray(reversedChars));
  };

  // Checks whether the given input text is equal to itself when reversed.
  public func isPalindrome(input : Text) : Bool {
    let reversed = reverseText(input);
    input == reversed
  };
}
