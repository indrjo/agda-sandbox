
module algebra.introduction where

open import Data.Product
open import Relation.Binary.PropositionalEquality

-- A magma is set together with a binary operation.
Magma = Σ Set (λ A → (A → A → A))

is-left-id : ∀ ((A , m) : Magma) → A → Set
is-left-id (A , m) e = ∀ (x : A) → m e x ≡ x

is-right-id : ∀ ((A , m) : Magma) → A → Set
is-right-id (A , m) e = ∀ (x : A) → m x e ≡ x

is-id : ∀ ((A , m) : Magma) → A → Set
is-id (A , m) e = is-left-id (A , m) e × is-right-id (A , m) e

id-uniq : ∀ ((A , m) : Magma)
        → ∀ (e₁ e₂ : A)
        → is-id (A , m) e₁
        → is-id (A , m) e₂
        → e₁ ≡ e₂
id-uniq (A , m) e₁ e₂ (e₁-is-lid , _) (_ , e₂-is-rid) =
{- Here is the strategy in words:
1. By e₁-is-lid, we have m e₁ e₂ ≡ e₂.
2. By e₂-is-rid, we have m e₁ e₂ ≡ e₁.
3. Just invoke a proper function ∀ {x y z} → x ≡ y → x ≡ z → y ≡ z.
-}
  trans (sym (e₂-is-rid e₁)) (e₁-is-lid e₂)

