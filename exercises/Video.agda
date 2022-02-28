open import Relation.Binary.PropositionalEquality
open import Data.List hiding (reverse)
open import Data.Nat
open import Data.Nat.Properties


rev : {A : Set} -> List A -> List A -> List A
rev acc [] = acc
rev acc (x ∷ xs) = rev (x ∷ acc) xs


reverse : {A : Set} -> List A -> List A
reverse xs = rev [] xs

length-reverse : {A : Set} -> {xs : List A} -> length (reverse xs) ≡ length xs
length-reverse {A} {xs = xs} = aux [] xs 
    where
        open ≡-Reasoning

        aux : (acc xs : List A) -> length (rev acc xs) ≡ length acc + length xs
        aux acc [] = sym (+-identityʳ (length acc))
        aux acc (x ∷ xs) = 
            begin
                length (rev acc (x ∷ xs)) ≡⟨ aux (x ∷ acc) xs ⟩
                suc (length acc + length xs) ≡⟨ sym ( +-suc (length acc) (length xs)) ⟩
                refl
        