
module natural-numbers where

-- Introduce the type of the natural numbers, written ℕ.
data ℕ : Set where
  zero : ℕ; suc : ℕ → ℕ

-- Induction principle.
ℕ-induction :
  ∀ (P : ℕ → Set) →
    P zero →
      (∀ (n : ℕ) → P n → P (suc n)) →
        ∀ (n : ℕ) → P n
ℕ-induction P x₀ step zero = x₀
ℕ-induction P x₀ step (suc n) = step n (ℕ-induction P x₀ step n)

-- RECURSION PRINCIPLE. For every C, f : C → C and x₀ : C there exists one
-- and only one g : ℕ → C such that
--         g 0 = x₀ and g (suc n) = f (g n).
-- We denote that g by ℕ-recursion C f x₀.
ℕ-recursion : ∀ (C : Set) → C → (C → C) → ℕ → C
ℕ-recursion C x₀ f n = ℕ-induction (λ _ → C) x₀ (λ _ → f) n

