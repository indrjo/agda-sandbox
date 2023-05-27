
module hello-products where

-- How do I write a family of types Xᵢ, for i : I?
--
-- >>> X : I → Set
--
-- How do I write a family of functions fᵢ : A → Xᵢ, for i : I?
--
-- >>> f : ∏ (i : I) A → Xᵢ
--
-- All this data induces the function
--
-- >>> func-prod f : A → ∏ (i : I) Xᵢ
-- >>> func-prod f a = λ i → f i a
--
-- How do I write all that in Agda?
--
-- ...
func-prod : ∀ {A : Set} → ∀ {I : Set} → ∀ {X : I → Set}
              → (∀ (i : I) → A → X i) → (A → ∀ (i : I) → X i)
func-prod f = λ a → (λ i → f i a)
