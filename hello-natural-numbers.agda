
module hello-natural-numbers where

-- Introduce the type of the natural numbers, written ℕ.
data ℕ : Set where
  -- the zero
  zero : ℕ
  -- the successor function
  succ : ℕ → ℕ

-- INDUCTION PRINCIPLE. We express this principle in a different way. Consider a sequence of
-- types X : ℕ → Set and suppose assigned one element x₀ : X 0. Let us introduce a family of
-- functions f n : X n → X (suc n), one for each n : ℕ. The idea is to provide a way to pass
-- from one type to the following one. We write this family as f : ∏ (n : ℕ) X n → X (suc n).
-- We want to build a sequence x : ∏ (n : ℕ) X n, starting from x 0 = x₀ and with f telling
-- from every x n : X n the term x (suc n) : X (suc n).
ℕ-induction : ∀ (X : ℕ → Set) → X zero → (∀ (n : ℕ) → X n → X (succ n)) → ∀ (n : ℕ) → X n
ℕ-induction X x₀ f zero = x₀
ℕ-induction X x₀ f (succ n) = f n (ℕ-induction X x₀ f n)

-- RECURSION PRINCIPLE. For every C, f : C → C and x₀ : C there exists one and only one map
-- g : ℕ → C such that g 0 = x₀ and g (suc n) = f (g n). We write g as ℕ-recursion C x₀ f.
ℕ-recursion : ∀ (C : Set) → C → (C → C) → ℕ → C
ℕ-recursion C x₀ f n = ℕ-induction (λ _ → C) x₀ (λ _ → f) n
