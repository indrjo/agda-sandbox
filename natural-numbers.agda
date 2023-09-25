module natural-numbers where

open import Data.Nat using (ℕ; zero; suc)
open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

-- INDUCTION PRINCIPLE. We express this principle in a different way. Consider a sequence of types
--
-- X : ℕ → Set
--
-- and suppose assigned one element
--
-- x₀ : X 0
--
-- Moreover consider a family of functions f n : X n → X (suc n), one for each n : ℕ, that is some
--
-- f : ∏ (n : ℕ) X n → X (suc n)
--
-- The idea is to provide a way to pass from one type, that is X n, to the next one, X (suc n).
-- Indeed, the exists one and only one 
--
-- x : ∏ (n : ℕ) X n
--
-- satisfying
--
-- x 0 = x₀
-- x (suc n) = f n (x n)
--
induction-principle = ∀ {n : Level}
                    → ∀ (X : ℕ → Set n)
                    → X zero
                    → (∀ (n : ℕ) → X n → X (suc n))
                    → ∀ (n : ℕ) → X n

-- RECURSION PRINCIPLE. For C, f : C → C and x₀ : C, there is one and only one x : ℕ → C such that
--
-- x 0 = x₀
-- x (suc n) = f (x n)
--
recursion-principle = ∀ {n : Level} → ∀ (C : Set n) → C → (C → C) → ℕ → C 

-- THEOREM. Induction Principle implies Recursion Principle.
induction-implies-recursion : induction-principle → recursion-principle
induction-implies-recursion induction C x₀ f = induction (λ _ → C) x₀ (λ _ → f)

-- Product of two types.
_×_ : ∀ {m n : Level} → Set m → Set n → Set (m ⊔ n)
A × B = Σ A (λ _ → B)

-- !!! Now do the converse: Recursion Priniciple implies Induction Principle.

-- PRIMITIVE RECURSION PRINCIPLE. For C, x₀ : C and f : ℕ × C → C, there is one and only one x : ℕ → C
-- such that
--
-- x 0 = x₀
-- x (suc n) = f n (x n)
--
primitive-recursion-principle = ∀ {n : Level} → ∀ (C : Set n) → C → (ℕ × C → C) → ℕ → C

-- THEOREM. Recursion Principle implies Primitive Recursion Principle.
recursion-implies-primitive-recursion : recursion-principle → primitive-recursion-principle
recursion-implies-primitive-recursion recursion C x₀ f n =
  snd (recursion (ℕ × C) (zero , x₀) (λ p → (suc (fst p) , f p)) n)

--primitive-recursion-implies-induction : primitive-recursion-principle → induction-principle
--primitive-recursion-implies-induction primitive-recursion X x₀ f n = ...
