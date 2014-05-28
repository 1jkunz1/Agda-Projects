module bool-todo where

open import lib

infixr 4 _imp_ 

_imp_ : 𝔹 → 𝔹 → 𝔹 
tt imp tt = tt
tt imp ff = ff
ff imp _ = tt

ff-imp : ∀ (b : 𝔹) → ff imp b ≡ tt
ff-imp _  = refl

imp-tt : ∀ (b : 𝔹) → b imp tt ≡ tt
imp-tt tt = refl
imp-tt ff = refl

imp-same : ∀ (b : 𝔹) → b imp b ≡ tt
imp-same tt = refl
imp-same ff = refl

&&-contra : ∀ (b : 𝔹) → b && ~ b ≡ ff
&&-contra tt = refl
&&-contra ff = refl

&&-comm : ∀ (b1 b2 : 𝔹) → b1 && b2 ≡ b2 && b1
&&-comm tt tt = refl
&&-comm tt ff = refl
&&-comm ff tt = refl
&&-comm ff ff = refl

||-comm : ∀ (b1 b2 : 𝔹) → b1 || b2 ≡ b2 || b1
||-comm tt tt = refl
||-comm tt ff = refl
||-comm ff tt = refl
||-comm ff ff = refl

&&-assoc : ∀ (b1 b2 b3 : 𝔹) → b1 && (b2 && b3) ≡ (b1 && b2) && b3
&&-assoc tt tt tt = refl
&&-assoc tt tt ff = refl
&&-assoc tt ff tt = refl
&&-assoc tt ff ff = refl
&&-assoc ff tt tt = refl
&&-assoc ff ff tt = refl
&&-assoc ff tt ff = refl
&&-assoc ff ff ff = refl

||-assoc : ∀ (b1 b2 b3 : 𝔹) → b1 || (b2 || b3) ≡ (b1 || b2) || b3
||-assoc tt tt tt = refl
||-assoc tt tt ff = refl
||-assoc tt ff ff = refl
||-assoc tt ff tt = refl
||-assoc ff tt tt = refl
||-assoc ff ff tt = refl
||-assoc ff tt ff = refl
||-assoc ff ff ff = refl

~-over-&& : ∀ (b1 b2 : 𝔹) → ~ ( b1 && b2 ) ≡ (~ b1 || ~ b2)
~-over-&& tt tt = refl
~-over-&& tt ff = refl
~-over-&& ff tt  = refl
~-over-&& ff ff = refl

imp-to-|| : ∀ (b1 b2 : 𝔹) → (b1 imp b2) ≡ (~ b1 || b2)
imp-to-|| tt tt = refl
imp-to-|| tt ff = refl
imp-to-|| ff tt = refl
imp-to-|| ff ff = refl


imp-ff : ∀ (b : 𝔹) → b imp ff ≡ ~ b
imp-ff tt = refl
imp-ff ff = refl

tt-imp : ∀ (b : 𝔹) → tt imp b ≡ b
tt-imp tt = refl
tt-imp ff = refl

