import M "mo:matchers/Matchers";
import Library "../src/Library";
import field "../src/core/field";
import group "../src/core/group";
import error "../src/core/error";
import scalar "../src/core/scalar";
import subtle "../src/subtle/lib";
import ecmult "../src/core/ecmult";
import S "mo:matchers/Suite";
import T "mo:matchers/Testable";

let suite = S.suite("isPalindrome", [
    S.test("anna is a palindrome",
      Library.isPalindrome("anna"),
      M.equals(T.bool(true))),
    S.test("christoph is not a palindrome",
      Library.isPalindrome("christoph"),
      M.equals(T.bool(false))),
]);

S.run(suite);
