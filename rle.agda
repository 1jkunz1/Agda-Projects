module rle where

open import lib

data run : Set where
  nonempty-run : 𝔹 → ℕ → (𝕃 ℕ) → run
  empty-run : run



-- 10 points
decode : run → 𝕃 𝔹
decode (nonempty-run b 0 []) = b :: []
decode (nonempty-run b 0 (n :: ns)) = b :: decode (nonempty-run (~ b) n ns)
decode (nonempty-run b (suc n) ns) = b :: (decode (nonempty-run b n ns))
decode empty-run = []

test-input : 𝕃 𝔹
test-input = ff :: tt :: tt :: tt :: ff :: ff :: []

decode-test1 = decode (nonempty-run ff 0 (2 :: 1 :: []))

-- 3 points for passing this test
lem-decode-test1 : decode-test1 ≡ test-input
lem-decode-test1 = refl

-- 1 point for passing this test
lem-decode-empty : decode empty-run ≡ []
lem-decode-empty = refl

{-

   Given a boolean b and a run encoding a list of booleans bs,
   construct a new run that encodes the list of booleans b :: bs.

-}
encodeh : 𝔹 → run → run
encodeh tt (nonempty-run tt n ns) = (nonempty-run tt (suc n) ns)
encodeh ff (nonempty-run ff n ns) = (nonempty-run ff (suc n) ns)
encodeh tt (nonempty-run ff n ns) = (nonempty-run tt 0 (n :: ns))
encodeh ff (nonempty-run tt n ns) = (nonempty-run ff 0 (n :: ns))
encodeh b empty-run = (nonempty-run b 0 [])

-- 10 points.  Hint: use encodeh in the case where the list is of the form (b :: bs).
encode : 𝕃 𝔹 → run
encode (b :: bs) = encodeh b (encode bs)
encode [] = empty-run

encode-test1 = encode test-input

-- 3 points for passing this test case
lem-encode-test1 : encode-test1 ≡ nonempty-run ff 0 (2 :: 1 :: [])
lem-encode-test1 = refl

-- 1 points for this test case
lem-encode-empty : encode [] ≡ empty-run 
lem-encode-empty = refl

-- 10 points (I found I needed this for decode-length below)
decode-length-neg : ∀ (b : 𝔹) (n : ℕ) (ns : 𝕃 ℕ) → length (decode (nonempty-run b n ns)) ≡ length (decode (nonempty-run (~ b) n ns))
decode-length-neg b 0 [] = refl
decode-length-neg b 0 (n :: ns) rewrite decode-length-neg (~ b) n ns = refl
decode-length-neg b (suc n) ns rewrite decode-length-neg b n ns = refl
