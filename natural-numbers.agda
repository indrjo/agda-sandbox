module hello-natural-numbers where

open import Data.Nat using (ℕ; zero; suc)
open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

-- INDUCTION PRINCIPLE. We express this principle in a different way. Consider a sequence of types
--
-- X : ℕ → Set
--
-- and suppose assigned one element
--
-- x₀ : X 0.
--
-- Moreover consider a family of functions f n : X n → X (suc n), one for each n : ℕ, that is some
--
-- f : ∏ (n : ℕ) X n → X (suc n)
--
-- The idea is to provide a way to pass from one type, that is X n, to the next one, X (suc n).
-- Aim: We want to build one
-- x : ∏ (n : ℕ) X n, starting from x 0 = x₀ and with f prescribing x (suc n) : X (suc n) from
-- x n : X n. We write such x as ℕ-induction X x₀ f.
--ℕ-induction-principle : Set₁
ℕ-induction-principle = ∀ {n : Level}
                      → ∀ (X : ℕ → Set n)
                      → X zero
                      → (∀ (n : ℕ) → X n → X (suc n))
                      → ∀ (n : ℕ) → X n
ℕ-induction : ℕ-induction-principle
ℕ-induction X x₀ f zero = x₀
ℕ-induction X x₀ f (suc n) = f n (ℕ-induction X x₀ f n)

-- THEOREM (Recursion Principle). For C, f : C → C and x₀ : C, there is one and only one g : ℕ → C
-- such that g 0 = x₀ and g (suc n) = f (g n). We write g as ℕ-recursion C x₀ f.
--ℕ-recursion-principle : Set₁
ℕ-recursion-principle = ∀ {n : Level} → ∀ (C : Set n) → C → (C → C) → ℕ → C 
ℕ-recursion : ℕ-recursion-principle
ℕ-recursion C x₀ f zero = x₀
ℕ-recursion C x₀ f (suc n) = f (ℕ-recursion C x₀ f n)

-- THEOREM. Induction Principle implies Recursion Principle
ℕ-induction->ℕ-recursion : ℕ-induction-principle → ℕ-recursion-principle
ℕ-induction->ℕ-recursion ℕ-ind C x₀ f = ℕ-ind (λ _ → C) x₀ (λ _ → f)

-- Pairs...
_×_ : ∀ {m n : Level} → Set m → Set n → Set (m ⊔ n)
A × B = Σ A (λ _ → B)

-- LEMMA?
ℕ-primitive-recursion-principle = ∀ {n : Level} → ∀ (C : Set n) → C → (ℕ × C → C) → ℕ → C
ℕ-primitive-recursion : ℕ-primitive-recursion-principle
ℕ-primitive-recursion C x₀ f n = snd (ℕ-recursion (ℕ × C) (zero , x₀) (λ p → (suc (fst p) , f p)) n)

-- !!! Now do the converse too.
{-
ℕ-recursion->ℕ-induction : ℕ-recursion-principle → ℕ-induction-principle
ℕ-recursion->ℕ-induction ℕ-rec X x₀ f zero = x₀
ℕ-recursion->ℕ-induction ℕ-rec X x₀ f (suc n) = f n (ℕ-rec (X n) x₀ f n)
-}
