{- A note on formalisation:
 - The proof in this file uses Agda as a meta-language for the DC
 - category. What has not been formalised in this proof is that DC
 - is a model of SDCC. The proof of this is however trivial on paper
 - but very annoying to formalise in Agda.
 - 
 - The use of function extensionality is simply to get around having
 - to use a more heavy-handed approach to environments than what can
 - be found in this file.
 -}
open import Agda.Builtin.Equality
open import Data.List

-- Technicalities for equality
trans : ∀ { A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

sym : ∀ { A : Set} { a b : A } → a ≡ b → b ≡ a
sym refl = refl

cong : ∀{A B : Set} {a₀ a₁ : A} → (f : A → B) → a₀ ≡ a₁ → (f a₀) ≡ (f a₁)
cong f refl = refl

cong2 : ∀{A B C : Set} {a₀ a₁ : A} → {b₀ b₁ : B} → (f : A → B → C) → a₀ ≡ a₁ → b₀ ≡ b₁ → (f a₀ b₀) ≡ (f a₁ b₁)
cong2 f refl refl = refl

cong3 : ∀{A B C D : Set} {a₀ a₁ : A} → {b₀ b₁ : B} → {c₀ c₁ : C}
      → (f : A → B → C → D) → a₀ ≡ a₁ → b₀ ≡ b₁ → c₀ ≡ c₁ → (f a₀ b₀ c₀) ≡ (f a₁ b₁ c₁)
cong3 f refl refl refl = refl

-- We are going to need this
postulate ext : ∀ {A B : Set} {f g : A -> B} -> (∀ z -> f z ≡ g z) -> f ≡ g

-- Assume a lattice
postulate L : Set
postulate _⊑_ : L → L → Set
postulate ⊑refl : {ℓ : L} → ℓ ⊑ ℓ

{- Representation of DCC types and terms -}
data Type : Set where
  unit  : Type
  _→'_  : Type → Type → Type
  _×'_  : Type → Type → Type
  _+'_  : Type → Type → Type
  T     : L → Type → Type

data _≼_ : L → Type → Set where
  PFlow     : ∀ {t ℓ ℓ'} → ℓ ⊑ ℓ' → ℓ ≼ (T ℓ' t)
  PInner    : ∀ {t ℓ ℓ'} → ℓ ≼ t → ℓ ≼ (T ℓ' t)
  PProduct  : ∀ {t s ℓ } → ℓ ≼ t → ℓ ≼ s → ℓ ≼ (s ×' t)
  PFunction : ∀ {t s ℓ } → ℓ ≼ t → ℓ ≼ (s →' t)

Ctx : Set
Ctx = List Type

data _∈_ : Type → Ctx → Set where
  hd : ∀ {t₀ Γ} → t₀ ∈ (t₀ ∷ Γ)
  tl : ∀ {t₀ t₁ Γ} → t₀ ∈ Γ → t₀ ∈ (t₁ ∷ Γ)

∈++ : ∀{x Γ Γ'} → x ∈ Γ → x ∈ (Γ' ++ Γ)
∈++ {Γ' = []} x₁ = x₁
∈++ {Γ' = x ∷ Γ'} x₁ = tl (∈++ x₁)

data Exp (Γ : Ctx) : Type → Set where
  Var  : ∀ {t}        → t ∈ Γ → Exp Γ t
  λ'   : ∀ {t₀ t₁}    → Exp (t₀ ∷ Γ) t₁ → Exp Γ (t₀ →' t₁)
  _•_  : ∀ {t₀ t₁}    → Exp Γ (t₀ →' t₁) → Exp Γ t₀ → Exp Γ t₁
  pair : ∀ {t₀ t₁}    → Exp Γ t₀ → Exp Γ t₁ → Exp Γ (t₀ ×' t₁)
  π₀   : ∀ {t₀ t₁}    → Exp Γ (t₀ ×' t₁) → Exp Γ t₀
  π₁   : ∀ {t₀ t₁}    → Exp Γ (t₀ ×' t₁) → Exp Γ t₁
  ι₀   : ∀ {t₀ t₁}    → Exp Γ t₀ → Exp Γ (t₀ +' t₁)
  ι₁   : ∀ {t₀ t₁}    → Exp Γ t₁ → Exp Γ (t₀ +' t₁)
  case : ∀ {t₀ t₁ t₂} → Exp Γ (t₀ +' t₁) → Exp Γ (t₀ →' t₂) → Exp Γ (t₁ →' t₂) → Exp Γ t₂
  η    : ∀ {t ℓ}      → Exp Γ t → Exp Γ (T ℓ t)
  bind : ∀ {t₀ t₁ ℓ}  → ℓ ≼ t₁ → Exp Γ (T ℓ t₀) → Exp Γ (t₀ →' t₁) → Exp Γ t₁
  <>   :                Exp Γ unit

data Exp₀ (Γ : Ctx) : Type → Set where
  Var  : ∀ {t}        → t ∈ Γ → Exp₀ Γ t
  λ'   : ∀ {t₀ t₁}    → Exp₀ (t₀ ∷ Γ) t₁ → Exp₀ Γ (t₀ →' t₁)
  _•_  : ∀ {t₀ t₁}    → Exp₀ Γ (t₀ →' t₁) → Exp₀ Γ t₀ → Exp₀ Γ t₁
  pair : ∀ {t₀ t₁}    → Exp₀ Γ t₀ → Exp₀ Γ t₁ → Exp₀ Γ (t₀ ×' t₁)
  π₀   : ∀ {t₀ t₁}    → Exp₀ Γ (t₀ ×' t₁) → Exp₀ Γ t₀
  π₁   : ∀ {t₀ t₁}    → Exp₀ Γ (t₀ ×' t₁) → Exp₀ Γ t₁
  ι₀   : ∀ {t₀ t₁}    → Exp₀ Γ t₀ → Exp₀ Γ (t₀ +' t₁)
  ι₁   : ∀ {t₀ t₁}    → Exp₀ Γ t₁ → Exp₀ Γ (t₀ +' t₁)
  case : ∀ {t₀ t₁ t₂} → Exp₀ Γ (t₀ +' t₁) → Exp₀ Γ (t₀ →' t₂) → Exp₀ Γ (t₁ →' t₂) → Exp₀ Γ t₂
  η    : ∀ {t ℓ}      → Exp₀ Γ t → Exp₀ Γ (T ℓ t)
  μ    : ∀ {t ℓ}      → Exp₀ Γ (T ℓ (T ℓ t)) → Exp₀ Γ (T ℓ t)
  fmap : ∀ {t t' ℓ}   → Exp₀ Γ (t →' t') → Exp₀ Γ (T ℓ t) → Exp₀ Γ (T ℓ t')
  up   : ∀ {t ℓ ℓ'}   → ℓ ⊑ ℓ' → Exp₀ Γ (T ℓ t) → Exp₀ Γ (T ℓ' t)
  com  : ∀ {t ℓ ℓ'}   → Exp₀ Γ (T ℓ (T ℓ' t)) → Exp₀ Γ (T ℓ' (T ℓ t))
  <>   :                Exp₀ Γ unit

-- Permutations and helpers
Superset : Ctx → Ctx → Set
Superset Γ' Γ = ∀ {x} → x ∈ Γ → x ∈ Γ'

Super-cons : ∀{Γ Γ' t} → Superset Γ' Γ → Superset (t ∷ Γ') (t ∷ Γ)
Super-cons x hd = hd
Super-cons x (tl x₁) = tl (x x₁)

Super-conss : ∀{Γ Γ' Γpre} → Superset Γ' Γ → Superset (Γpre ++ Γ') (Γpre ++ Γ)
Super-conss {Γpre = []} x = x
Super-conss {Γpre = x₁ ∷ Γpre} x = Super-cons (Super-conss x)

Super-++ : ∀{Γ Γ'} → Superset (Γ' ++ Γ) Γ
Super-++ x₁ = ∈++ x₁

multiple-conss : ∀{Γ Γ' Γ'' Γpre t}
               → (p : Superset Γ' Γ)
               → (q : Superset Γ'' Γ')
               → (x : t ∈ (Γpre ++ Γ))
               → Super-conss {Γpre = Γpre} q (Super-conss {Γpre = Γpre} p x)
               ≡ Super-conss {Γpre = Γpre} (λ z → q (p z)) x
multiple-conss {Γpre = []} p q x = refl
multiple-conss {Γpre = x₁ ∷ Γpre} p q hd = refl
multiple-conss {Γpre = x₁ ∷ Γpre} p q (tl x) = cong tl (multiple-conss p q x)

-- Typing stuff
weaken : ∀{Γ Γ' t₂} → Superset Γ' Γ → Exp Γ t₂ → Exp Γ' t₂
weaken x <> = <>
weaken {t₂ = t₂} x (Var x₁) = Var (x x₁)
weaken x (λ' {t₀} x₁) = λ' (weaken (Super-cons x) x₁)
weaken x (x₁ • x₂) = (weaken x x₁) • (weaken x x₂)
weaken x (pair x₁ x₂) = pair (weaken x x₁) (weaken x x₂)
weaken x (π₀ x₁) = π₀ (weaken x x₁)
weaken x (π₁ x₁) = π₁ (weaken x x₁)
weaken x (ι₀ x₁) = ι₀ (weaken x x₁)
weaken x (ι₁ x₁) = ι₁ (weaken x x₁)
weaken x (case x₁ x₂ x₃) = case (weaken x x₁) (weaken x x₂) (weaken x x₃)
weaken x (η x₁) = η (weaken x x₁)
weaken x (bind x₁ x₂ x₃) = bind x₁ (weaken x x₂) (weaken x x₃)

weaken-compose : ∀{Γ Γ' Γ'' Γpre t} → (e : Exp (Γpre ++ Γ) t) → (p : Superset Γ' Γ) → (q : Superset Γ'' Γ')
               → weaken (Super-conss {Γpre = Γpre} q) (weaken (Super-conss {Γpre = Γpre} p) e)
               ≡ weaken (Super-conss {Γpre = Γpre} (λ z → q (p z))) e
weaken-compose (Var x) p q = cong Var (multiple-conss p q x)
weaken-compose {Γpre = Γpre} (λ' {t₀} e) p q = cong λ' (weaken-compose {Γpre = t₀ ∷ Γpre} e p q)
weaken-compose (e • e₁) p q = cong2 _•_ (weaken-compose e p q) (weaken-compose e₁ p q)
weaken-compose (pair e e₁) p q = cong2 pair (weaken-compose e p q) (weaken-compose e₁ p q)
weaken-compose (π₀ e) p q = cong π₀ (weaken-compose e p q)
weaken-compose (π₁ e) p q = cong π₁ (weaken-compose e p q)
weaken-compose (ι₀ e) p q = cong ι₀ (weaken-compose e p q)
weaken-compose (ι₁ e) p q = cong ι₁ (weaken-compose e p q)
weaken-compose (case e e₁ e₂) p q = cong3 case (weaken-compose e p q) (weaken-compose e₁ p q) (weaken-compose e₂ p q)
weaken-compose (η e) p q = cong η (weaken-compose e p q)
weaken-compose (bind x e e₁) p q = cong2 (bind x) (weaken-compose e p q) (weaken-compose e₁ p q)
weaken-compose <> p q = refl

-- Typing stuff
weaken₀ : ∀{Γ Γ' t₂} → Superset Γ' Γ → Exp₀ Γ t₂ → Exp₀ Γ' t₂
weaken₀ x <> = <>
weaken₀ {t₂ = t₂} x (Var x₁) = Var (x x₁)
weaken₀ x (λ' {t₀} x₁) = λ' (weaken₀ (Super-cons x) x₁)
weaken₀ x (x₁ • x₂) = (weaken₀ x x₁) • (weaken₀ x x₂)
weaken₀ x (pair x₁ x₂) = pair (weaken₀ x x₁) (weaken₀ x x₂)
weaken₀ x (π₀ x₁) = π₀ (weaken₀ x x₁)
weaken₀ x (π₁ x₁) = π₁ (weaken₀ x x₁)
weaken₀ x (ι₀ x₁) = ι₀ (weaken₀ x x₁)
weaken₀ x (ι₁ x₁) = ι₁ (weaken₀ x x₁)
weaken₀ x (case x₁ x₂ x₃) = case (weaken₀ x x₁) (weaken₀ x x₂) (weaken₀ x x₃)
weaken₀ x (η x₁) = η (weaken₀ x x₁)
weaken₀ x (up p t) = up p (weaken₀ x t)
weaken₀ x (com t) = com (weaken₀ x t)
weaken₀ x (μ t) = μ (weaken₀ x t)
weaken₀ x (fmap f t) = fmap (weaken₀ x f) (weaken₀ x t)

-- Some commonality here which I can't be bothered to figure out
lemma-conss : ∀{Γ Γ' Γpre : Ctx}{t t' : Type} → (p : Superset Γ' Γ)
            → (x : t ∈ (Γpre ++ Γ))
            → Super-conss {Γpre = Γpre} (Super-cons {t = t'} p) (Super-conss tl x)
            ≡ Super-conss tl (Super-conss p x)
lemma-conss {Γpre = []} p x = refl
lemma-conss {Γpre = x₁ ∷ Γpre} p hd = refl
lemma-conss {Γpre = x₁ ∷ Γpre} p (tl x) = cong tl (lemma-conss p x)

lemma-conss-id : ∀{Γpre Γ t} → (x : t ∈ (Γpre ++ Γ))
               → Super-conss {Γpre = Γpre} (λ z → z) x ≡ x
lemma-conss-id {[]} x = refl
lemma-conss-id {x₁ ∷ Γpre} hd = refl
lemma-conss-id {x₁ ∷ Γpre} (tl x) = cong tl (lemma-conss-id {Γpre = Γpre} x)

weaken-sctl₀ : ∀{Γ Γ' Γpre t t'}
             → (p : Superset Γ' Γ) → (e : Exp₀ (Γpre ++ Γ) t)
             → weaken₀ (Super-conss {Γpre = Γpre} (Super-cons {t = t'} p)) (weaken₀ (Super-conss {Γpre = Γpre} tl) e)
             ≡ weaken₀ (Super-conss {Γpre = Γpre} tl) (weaken₀ (Super-conss {Γpre = Γpre} p) e)
weaken-sctl₀ p (Var x) = cong Var (lemma-conss p x)
weaken-sctl₀ {Γpre = Γpre} p (λ' {t₀ = t₀} e) = cong λ' (weaken-sctl₀ {Γpre = t₀ ∷ Γpre} p e)
weaken-sctl₀ p (e • e₁) = cong2 _•_ (weaken-sctl₀ p e) (weaken-sctl₀ p e₁)
weaken-sctl₀ p (pair e e₁) = cong2 pair (weaken-sctl₀ p e) (weaken-sctl₀ p e₁)
weaken-sctl₀ p (π₀ e) = cong π₀ (weaken-sctl₀ p e)
weaken-sctl₀ p (π₁ e) = cong π₁ (weaken-sctl₀ p e)
weaken-sctl₀ p (ι₀ e) = cong ι₀ (weaken-sctl₀ p e)
weaken-sctl₀ p (ι₁ e) = cong ι₁ (weaken-sctl₀ p e)
weaken-sctl₀ p (case e e₁ e₂) = cong3 case (weaken-sctl₀ p e) (weaken-sctl₀ p e₁) (weaken-sctl₀ p e₂)
weaken-sctl₀ p (η e) = cong η (weaken-sctl₀ p e)
weaken-sctl₀ p (μ e) = cong μ (weaken-sctl₀ p e)
weaken-sctl₀ p (fmap e e₁) = cong2 fmap (weaken-sctl₀ p e) (weaken-sctl₀ p e₁)
weaken-sctl₀ p (up x e) = cong (up x) (weaken-sctl₀ p e)
weaken-sctl₀ p (com e) = cong com (weaken-sctl₀ p e)
weaken-sctl₀ p <> = refl

weaken-sctl : ∀{Γ Γ' Γpre t t'}
            → (p : Superset Γ' Γ) → (e : Exp (Γpre ++ Γ) t)
            → weaken (Super-conss {Γpre = Γpre} (Super-cons {t = t'} p)) (weaken (Super-conss {Γpre = Γpre} tl) e)
            ≡ weaken (Super-conss {Γpre = Γpre} tl) (weaken (Super-conss {Γpre = Γpre} p) e)
weaken-sctl p (Var x) = cong Var (lemma-conss p x)
weaken-sctl {Γpre = Γpre} p (λ' {t₀ = t₀} e) = cong λ' (weaken-sctl {Γpre = t₀ ∷ Γpre} p e)
weaken-sctl p (e • e₁) = cong2 _•_ (weaken-sctl p e) (weaken-sctl p e₁)
weaken-sctl p (pair e e₁) = cong2 pair (weaken-sctl p e) (weaken-sctl p e₁)
weaken-sctl p (π₀ e) = cong π₀ (weaken-sctl p e)
weaken-sctl p (π₁ e) = cong π₁ (weaken-sctl p e)
weaken-sctl p (ι₀ e) = cong ι₀ (weaken-sctl p e)
weaken-sctl p (ι₁ e) = cong ι₁ (weaken-sctl p e)
weaken-sctl p (case e e₁ e₂) = cong3 case (weaken-sctl p e) (weaken-sctl p e₁) (weaken-sctl p e₂)
weaken-sctl p (η e) = cong η (weaken-sctl p e)
weaken-sctl p (bind x e e₁) = cong2 (bind x) (weaken-sctl p e) (weaken-sctl p e₁)
weaken-sctl p <> = refl

bind* : ∀{ℓ Γ t t'} → ℓ ≼ t' → Exp₀ Γ (T ℓ t) → Exp₀ Γ (t →' t') → Exp₀ Γ t'
bind* (PFlow x) x₁ x₂ = μ (up x (fmap x₂ x₁))
bind* (PInner x) x₁ x₂ = fmap (λ' (bind* x (Var hd) (λ' (Var hd)))) (com (fmap x₂ x₁))
bind* (PProduct x x₃) x₁ x₂ = pair (bind* x₃ x₁ (λ' (π₀ (weaken₀ tl x₂ • Var hd)))) (bind* x x₁ (λ' (π₁ (weaken₀ tl x₂ • Var hd))))
bind* (PFunction x) x₁ x₂ = λ' (bind* x (weaken₀ tl x₁) (λ' ((weaken₀ (λ z → tl (tl z)) x₂ • Var hd) • Var (tl hd))))

_↓ : ∀{Γ t} → Exp Γ t → Exp₀ Γ t
Var x ↓ = Var x
λ' e ↓ = λ' (e ↓)
(e • e₁) ↓ = (e ↓) • (e₁ ↓)
pair e e₁ ↓ = pair (e ↓) (e₁ ↓)
π₀ e ↓ = π₀ (e ↓)
π₁ e ↓ = π₁ (e ↓)
ι₀ e ↓ = ι₀ (e ↓)
ι₁ e ↓ = ι₁ (e ↓)
case e e₁ e₂ ↓ = case (e ↓) (e₁ ↓) (e₂ ↓)
η e ↓ = η (e ↓)
bind x e e₁ ↓ = bind* x (e ↓) (e₁ ↓)
<> ↓ = <>

_↑ : ∀{Γ t} → Exp₀ Γ t → Exp Γ t
Var x ↑ = Var x
λ' e ↑ = λ' (e ↑)
(e • e₁) ↑ = (e ↑) • (e₁ ↑)
pair e e₁ ↑ = pair (e ↑) (e₁ ↑)
π₀ e ↑ = π₀ (e ↑)
π₁ e ↑ = π₁ (e ↑)
ι₀ e ↑ = ι₀ (e ↑)
ι₁ e ↑ = ι₁ (e ↑)
case e e₁ e₂ ↑ = case (e ↑) (e₁ ↑) (e₂ ↑)
η e ↑ = η (e ↑)
μ e ↑ = bind (PFlow ⊑refl) (e ↑) (λ' (Var hd))
fmap e e₁ ↑ = bind (PFlow ⊑refl) (e₁ ↑) (λ' (η (weaken tl (e ↑) • Var hd)))
up x e ↑ = bind (PFlow x) (e ↑) (λ' (η (Var hd)))
com e ↑ = bind (PInner (PFlow ⊑refl)) (e ↑) (λ' (bind (PFlow ⊑refl) (Var hd) (λ' (η (η (Var hd))))))
<> ↑ = <>


weaken-sctl-2 : ∀{Γ Γ' Γ'' t t₀ t₁}
              → (p : Superset Γ' Γ)
              → (q : Superset Γ'' Γ')
              → (e : Exp Γ t)
              → weaken (λ z → tl (tl z)) (weaken (λ z → q (p z)) e)
              ≡ weaken (Super-cons {t = t₀} (Super-cons {t = t₁} q))
                (weaken (Super-cons {t = t₀} (Super-cons {t = t₁} p))
                (weaken (λ z → tl (tl z)) e))
weaken-sctl-2 p q e =
  trans (sym (weaken-compose {Γpre = []} (weaken (λ z → q (p z)) e) tl tl))
  (trans (cong (λ ex → weaken tl (weaken tl ex)) (sym (weaken-compose {Γpre = []} e p q)))
  (trans (cong (weaken tl) (sym (weaken-sctl {Γpre = []} q (weaken p e))))
  (trans (sym (weaken-sctl {Γpre = []} (Super-cons q) (weaken tl (weaken p e))))
  (cong (weaken (Super-cons (Super-cons q)))
  (trans (cong (weaken tl) (sym (weaken-sctl {Γpre = []} p e)))
  (trans (sym (weaken-sctl {Γpre = []} (Super-cons p) (weaken tl e)))
  (cong (λ e₁ → weaken (Super-cons (Super-cons p)) e₁)
  (weaken-compose {Γpre = []} e tl tl))))))))

weaken-sctl-2' : ∀{Γ Γ' t t₀ t₁}
               → (p : Superset Γ' Γ)
               → (e : Exp Γ t)
               → weaken (Super-cons (Super-cons p)) (weaken (λ z → tl {t₁ = t₀} (tl {t₁ = t₁} z)) e)
               ≡ weaken (λ z → tl (tl z)) (weaken p e)
weaken-sctl-2' p e =
  trans (sym  (cong (λ e₁ → weaken (Super-cons (Super-cons p)) e₁)   (weaken-compose {Γpre = []} e tl tl)))
  (trans (weaken-sctl {Γpre = []} (Super-cons p) (weaken tl e))
  (trans (cong (weaken tl) (weaken-sctl {Γpre = []} p e))
  (weaken-compose {Γpre = []} (weaken p e) tl tl)))

weaken-sctl-mix : ∀{Γ Γ' t t₀ t₁} → (e : Exp Γ t) → (p : Superset Γ' (t₀ ∷ Γ))
                → weaken (Super-cons {t = t₁} p) (weaken (λ z → tl (tl z)) e)
                ≡ weaken (λ z → tl {t₁ = t₁} (p (tl {t₁ = t₀} z))) e
weaken-sctl-mix e p =
  trans (cong (weaken (Super-cons p)) (sym (weaken-compose {Γpre = []} e tl tl)))
  (trans (weaken-sctl {Γpre = []} p (weaken tl e))
  (trans (weaken-compose {Γpre = []} (weaken tl e) p tl)
  (weaken-compose {Γpre = []} e (λ {x} → tl) λ {x} z → tl (p z))))

-- Middle-of-the-night equational reasoning :S
weaken-bind : ∀{Γ Γ' Γ'' t t' ℓ}
            → (x : ℓ ≼ t')
            → (p : Superset Γ' Γ) 
            → (q : Superset Γ'' Γ')
            → (e : Exp Γ (T ℓ t))
            → (e' : Exp Γ (t →' t'))
            → (∀{Γ' Γ''} → (p : Superset Γ' Γ) → (q : Superset Γ'' Γ') → weaken q (weaken p e) ↓  ≡ weaken₀ q (weaken p e ↓))
            → (∀{Γ' Γ''} → (p : Superset Γ' Γ) → (q : Superset Γ'' Γ') → weaken q (weaken p e') ↓ ≡ weaken₀ q (weaken p e' ↓))
            → bind* x (weaken q (weaken p e) ↓) (weaken q (weaken p e') ↓) ≡ weaken₀ q (bind* x (weaken p e ↓) (weaken p e' ↓))
weaken-bind (PFlow x) p q e e' x₁ x₂ = cong2 (λ e₀ e₁ → μ (up x (fmap e₀ e₁))) (x₂ p q) (x₁ p q)
weaken-bind (PInner x) p q e e' x₁ x₂ =
  let ih = weaken-bind x (Super-cons p) (Super-cons q) (Var hd) (λ' (Var hd)) (λ p q → refl) (λ p q → refl) in
  cong3 (λ b e'' e₁ → fmap (λ' b) (com (fmap e'' e₁))) ih (x₂ p q) (x₁ p q)
weaken-bind (PProduct x x₃) p q e e' x₁ x₂ =
     let ih₀ = weaken-bind x₃ p q e (λ' (π₀ (weaken tl e' • Var hd))) x₁ λ p₁ q₁ →
               trans (cong (λ ex → λ' (π₀ ((weaken (Super-cons q₁) ex ↓) • Var hd)))  (weaken-compose e' tl (Super-cons p₁)))
               (trans (cong (λ ex → λ' (π₀ (ex • Var hd))) (x₂ (λ z → tl (p₁ z)) (Super-cons q₁)))
               (cong (λ ex → λ' (π₀ (weaken₀ (Super-cons q₁) ex • Var hd)))
               (cong _↓ (sym (weaken-compose e' tl (Super-cons p₁))))))
  in let ih₁ = weaken-bind x p q e (λ' (π₁ (weaken tl e' • Var hd))) x₁ λ p₁ q₁ →
               trans (cong (λ ex → λ' (π₁ ((weaken (Super-cons q₁) ex ↓) • Var hd)))  (weaken-compose e' tl (Super-cons p₁)))
               (trans (cong (λ ex → λ' (π₁ (ex • Var hd))) (x₂ (λ z → tl (p₁ z)) (Super-cons q₁)))
               (cong (λ ex → λ' (π₁ (weaken₀ (Super-cons q₁) ex • Var hd)))
               (cong _↓ (sym (weaken-compose e' tl (Super-cons p₁))))))
  in cong2 pair (trans (cong  (λ ex → bind* x₃ (weaken q (weaken p e) ↓) (λ' (π₀ (ex • Var hd))))
                (trans (cong (weaken₀ tl) (cong _↓ (weaken-compose e' p q)))
                (trans (sym (x₂ (Super-conss (λ {x₄} z → q (p z))) λ {x₄} → tl))
                (trans (sym (cong (λ ex → weaken tl ex ↓) (weaken-compose e' p q)))
                (trans (sym (cong _↓ (weaken-sctl q (weaken p e'))))
                (cong (λ ex → weaken (Super-cons q) ex ↓) (sym (weaken-sctl p e'))))))))
                (trans ih₀ (cong (λ ex → weaken₀ q (bind* x₃ (weaken p e ↓) (λ' (π₀ (ex • Var hd)))))
                                          (trans (cong _↓ (weaken-sctl {Γpre = []} p e')) (x₂ (Super-conss p)
                                          (tl))))))

                (trans (cong  (λ ex → bind* x (weaken q (weaken p e) ↓) (λ' (π₁ (ex • Var hd))))
                (trans (cong (weaken₀ tl) (cong _↓ (weaken-compose e' p q)))
                (trans (sym (x₂ (Super-conss (λ {x₄} z → q (p z))) λ {x₄} → tl))
                (trans (sym (cong (λ ex → weaken tl ex ↓) (weaken-compose e' p q)))
                (trans (sym (cong _↓ (weaken-sctl q (weaken p e'))))
                (cong (λ ex → weaken (Super-cons q) ex ↓) (sym (weaken-sctl p e'))))))))
                (trans ih₁ (cong  (λ ex → weaken₀ q (bind* x (weaken p e ↓) (λ' (π₁ (ex • Var hd)))))
                           (trans (cong _↓ (weaken-sctl {Γpre = []} p e'))
                           (x₂ (Super-conss p) tl)))))
weaken-bind (PFunction x) p q e e' x₁ x₂ =
  let ih = weaken-bind x (Super-cons p)
                         (Super-cons q)
                         (weaken tl e)
                         (λ' ((weaken (λ z → tl (tl z)) e' • Var hd) • Var (tl hd)))
                         (λ p₁ q → trans (cong (λ ex → weaken q ex ↓) (weaken-compose {Γpre = []} e (λ {x₃} → tl) p₁))
                                  (trans (x₁ (λ z → p₁ (tl z)) q)
                                  (cong (λ ex → weaken₀ q (ex ↓)) (sym (weaken-compose {Γpre = []} e tl p₁)))))
                         λ p₁ q₁ →
                  (cong (λ ex → λ' ((ex • Var hd) • Var (tl (q₁ (p₁ hd)))))
                  (trans (trans (cong (λ ex → weaken (Super-cons q₁) ex ↓) (weaken-sctl-mix e' p₁))
                  (x₂ (λ z → Super-cons p₁ (tl (tl z))) (Super-cons q₁)))
                  (cong (weaken₀ (Super-cons q₁)) (cong _↓ (sym (weaken-sctl-mix {t = _} e' p₁))))))
  in cong λ' (trans (cong2 (λ ex₀ ex₁ → bind* x ex₀ (λ' ((ex₁ • Var hd) • Var (tl hd))))
                    (trans (cong (λ ex → weaken₀ tl (ex ↓)) (weaken-compose {Γpre = []} e p q))
                    (trans (sym (x₁ (Super-conss (λ {x₃} z → q (p z))) λ {x₃} → tl))
                    (trans (cong (λ ex → weaken tl ex ↓) (sym (weaken-compose {Γpre = []} e p q)))
                    (trans (cong _↓ (sym (weaken-sctl q (weaken p e))))
                    ((cong (λ ex → weaken (Super-cons q) ex ↓) (sym (weaken-sctl p e)))
                    )))))
                    (trans (cong (λ ex → weaken₀ (λ z → tl (tl z)) (ex ↓))   (weaken-compose {Γpre = []} e' p q))
                    (trans (sym (x₂ (Super-conss (λ {x₃} z → q (p z))) λ {x₃} z → tl (tl z)))
                    (cong _↓ (weaken-sctl-2 p q e')))))
             (trans ih (cong2  (λ ex₀ ex₁ → weaken₀ (Super-cons q) (bind* x ex₀ (λ' ((ex₁ • Var hd) • Var (tl hd)))))
                       (trans (cong _↓ (weaken-sctl {Γpre = []} p e)) (x₁ p tl))
                       (trans (cong _↓ (weaken-sctl-2' p e')) (x₂ p (λ z → tl (tl z)))))))

weaken↓2 : ∀{Γ Γ' Γ'' t} → (p : Superset Γ' Γ) → (q : Superset Γ'' Γ') → (e : Exp Γ t)
         → weaken q (weaken p e) ↓ ≡ weaken₀ q (weaken p e ↓)
weaken↓2 p q (Var x) = refl
weaken↓2 p q (λ' e) = cong λ' (weaken↓2 (Super-cons p) (Super-cons q) e)
weaken↓2 p q (e • e₁) = cong2 _•_ (weaken↓2 p q e) (weaken↓2 p q e₁)
weaken↓2 p q (pair e e₁) = cong2 pair (weaken↓2 p q e) (weaken↓2 p q e₁)
weaken↓2 p q (π₀ e) = cong π₀ (weaken↓2 p q e)
weaken↓2 p q (π₁ e) = cong π₁ (weaken↓2 p q e)
weaken↓2 p q (ι₀ e) = cong ι₀ (weaken↓2 p q e)
weaken↓2 p q (ι₁ e) = cong ι₁ (weaken↓2 p q e)
weaken↓2 p q (case e e₁ e₂) = cong3 case (weaken↓2 p q e) (weaken↓2 p q e₁) (weaken↓2 p q e₂)
weaken↓2 p q (η e) = cong η (weaken↓2 p q e)
weaken↓2 p q (bind x e e₁) = weaken-bind x p q e e₁ (λ p₁ q₁ → weaken↓2 p₁ q₁ e) (λ p₁ q₁ → weaken↓2 p₁ q₁ e₁)
weaken↓2 p q <> = refl

weaken-id : ∀{Γpre Γ t} → (e : Exp (Γpre ++ Γ) t) → weaken (Super-conss {Γpre = Γpre} (λ z → z)) e ≡ e
weaken-id {Γpre = Γpre} (Var x) = cong Var (lemma-conss-id {Γpre = Γpre} x)
weaken-id {Γpre = Γpre} (λ' {t₀ = t₀} e) = cong λ' (weaken-id {Γpre = t₀ ∷ Γpre} e)
weaken-id {Γpre = Γpre} (e • e₁) = cong2 _•_ (weaken-id {Γpre = Γpre} e) (weaken-id {Γpre = Γpre} e₁)
weaken-id {Γpre = Γpre} (pair e e₁) = cong2 pair (weaken-id {Γpre} e) (weaken-id {Γpre} e₁)
weaken-id {Γpre = Γpre} (π₀ e) = cong π₀ (weaken-id {Γpre} e)
weaken-id {Γpre = Γpre} (π₁ e) = cong π₁ (weaken-id {Γpre} e)
weaken-id {Γpre = Γpre} (ι₀ e) = cong ι₀ (weaken-id {Γpre} e)
weaken-id {Γpre = Γpre} (ι₁ e) = cong ι₁ (weaken-id {Γpre} e)
weaken-id {Γpre = Γpre} (case e e₁ e₂) = cong3 case  (weaken-id {Γpre} e) (weaken-id {Γpre} e₁) (weaken-id {Γpre} e₂)
weaken-id {Γpre = Γpre} (η e) = cong η (weaken-id {Γpre} e)
weaken-id {Γpre = Γpre} (bind x e e₁) = cong2 (bind x) (weaken-id {Γpre} e) (weaken-id {Γpre} e₁)
weaken-id <> = refl

weaken↓ : ∀{Γ Γ' t} → (p : Superset Γ' Γ) → (e : Exp Γ t) → weaken p e ↓ ≡ weaken₀ p (e ↓)
weaken↓ p e =
  let helper = weaken↓2 (λ z → z) p e
  in trans (sym (cong (λ ex → weaken p ex ↓) (weaken-id {Γpre = []} e)))
    (trans helper
    (cong (λ ex → weaken₀ p (ex ↓)) (weaken-id {Γpre = []} e)))

{- Embedding in Agda -}
data _×_ : Set → Set → Set where
  _,_ : ∀ {A B} → A → B → A × B

fst : ∀{A B} → A × B → A
fst (x , x₁) = x

snd : ∀{A B} → A × B → B
snd (x , x₁) = x₁

data _+_ : Set → Set → Set where
  inl : {A B : Set} → A → A + B
  inr : {A B : Set} → B → A + B

caseOn : ∀{A B} → {C : Set} → (A + B) → (A → C) → (B → C) → C
caseOn (inl x) x₁ x₂ = x₁ x
caseOn (inr x) x₁ x₂ = x₂ x

data ⊤ : Set where
  <>' : ⊤

data ⊥ : Set where

-- Types
type : Type → Set
type unit      = ⊤
type (x →' x₂) = type x → type x₂
type (x ×' x₂) = type x × type x₂
type (x +' x₂) = type x + type x₂
type (T ℓ x₂)  = type x₂

-- Environments
env : Ctx → Set
env Γ = ∀ { t } → t ∈ Γ → type t

empty : env []
empty ()

extend : ∀{Γ} → env Γ → (t : Type) → type t → env (t ∷ Γ)
extend x t x₁ hd = x₁
extend x t x₁ (tl x₂) = x x₂

extend-cons : ∀{Γ Γ' t t' z}{p : Superset Γ' Γ} → (en : env Γ) → (en' : env Γ')
            → (∀{t}{x : t ∈ Γ} → en x ≡ en' (p x))
            → (x : t ∈ (t' ∷ Γ))
            → extend en t' z x ≡ extend en' t' z (Super-cons p x)
extend-cons en en' x hd = refl
extend-cons en en' x (tl x₁) = x

⟦_⟧ : ∀{Γ t} → Exp Γ t → env Γ → type t
⟦ Var x ⟧ en = en x
⟦ λ' e ⟧ en = λ x → ⟦ e ⟧ (extend en _ x)
⟦ e • e₁ ⟧ en = ⟦ e ⟧ en (⟦ e₁ ⟧ en)
⟦ pair e e₁ ⟧ en = ⟦ e ⟧ en , ⟦ e₁ ⟧ en
⟦ π₀ e ⟧ en = fst (⟦ e ⟧ en)
⟦ π₁ e ⟧ en = snd (⟦ e ⟧ en)
⟦ ι₀ e ⟧ en = inl (⟦ e ⟧ en)
⟦ ι₁ e ⟧ en = inr (⟦ e ⟧ en)
⟦ case e e₁ e₂ ⟧ en = caseOn (⟦ e ⟧ en) (⟦ e₁ ⟧ en) (⟦ e₂ ⟧ en)
⟦ η e ⟧ en = ⟦ e ⟧ en
⟦ bind x e e₁ ⟧ en = ⟦ e₁ ⟧ en (⟦ e ⟧ en)
⟦ <> ⟧ en = <>'

weaken-tl : ∀{Γ Γ' t}
          → (p : Superset Γ' Γ)
          → (e : Exp Γ t)
          → (en : env Γ) → (en' : env Γ')
          → (∀{t}{x : t ∈ Γ} → en x ≡ en' (p x))
          → ⟦ weaken p e ⟧ en' ≡ ⟦ e ⟧ en
weaken-tl p (Var x₁) en en' x = sym x
weaken-tl p (λ' {t₀} e) en en' x = ext λ x₁ → weaken-tl (Super-cons p) e
                                                        (extend en t₀ x₁)
                                                        (extend en' t₀ x₁)
                                                        λ {t} {x₂} → extend-cons en en' x x₂
weaken-tl p (e • e₁) en en' x = cong2 (λ f x₁ → f x₁) (weaken-tl p e en en' x) (weaken-tl p e₁ en en' x)
weaken-tl p (pair e e₁) en en' x = cong2 _,_ (weaken-tl p e en en' x) (weaken-tl p e₁ en en' x)
weaken-tl p (π₀ e) en en' x = cong fst (weaken-tl p e en en' x)
weaken-tl p (π₁ e) en en' x = cong snd (weaken-tl p e en en' x)
weaken-tl p (ι₀ e) en en' x = cong inl (weaken-tl p e en en' x)
weaken-tl p (ι₁ e) en en' x = cong inr (weaken-tl p e en en' x)
weaken-tl p (case e e₁ e₂) en en' x = cong3 caseOn (weaken-tl p e en en' x) (weaken-tl p e₁ en en' x) (weaken-tl p e₂ en en' x)
weaken-tl p (η e) en en' x = weaken-tl p e en en' x
weaken-tl p (bind x₁ e e₁) en en' x = cong2 (λ f x₂ → f x₂) (weaken-tl p e₁ en en' x) (weaken-tl p e en en' x)
weaken-tl p <> en en' x = refl

⟦_⟧₀ : ∀{Γ t} → Exp₀ Γ t → env Γ → type t
⟦ Var x ⟧₀ en = en x
⟦ λ' e ⟧₀ en = λ x → ⟦ e ⟧₀ (extend en _ x)
⟦ e • e₁ ⟧₀ en = ⟦ e ⟧₀ en (⟦ e₁ ⟧₀ en)
⟦ pair e e₁ ⟧₀ en = ⟦ e ⟧₀ en , ⟦ e₁ ⟧₀ en
⟦ π₀ e ⟧₀ en = fst (⟦ e ⟧₀ en)
⟦ π₁ e ⟧₀ en = snd (⟦ e ⟧₀ en)
⟦ ι₀ e ⟧₀ en = inl (⟦ e ⟧₀ en)
⟦ ι₁ e ⟧₀ en = inr (⟦ e ⟧₀ en)
⟦ case e e₁ e₂ ⟧₀ en = caseOn (⟦ e ⟧₀ en) (⟦ e₁ ⟧₀ en) (⟦ e₂ ⟧₀ en)
⟦ η e ⟧₀ en = ⟦ e ⟧₀ en
⟦ μ e ⟧₀ en = ⟦ e ⟧₀ en
⟦ up x e ⟧₀ en = ⟦ e ⟧₀ en
⟦ com e ⟧₀ en = ⟦ e ⟧₀ en
⟦ fmap f e ⟧₀ en = ⟦ f ⟧₀ en (⟦ e ⟧₀ en)
⟦ <> ⟧₀ en = <>'

weaken-tl₀ : ∀{Γ Γ' t}
           → (p : Superset Γ' Γ)
           → (e : Exp₀ Γ t)
           → (en : env Γ)
           → (en' : env Γ')
           → (∀{t}{x : t ∈ Γ} → en x ≡ en' (p x))
           → (⟦ (weaken₀ p e) ⟧₀ en') ≡ (⟦ e ⟧₀ en)
weaken-tl₀ p (Var x₁) en en' x = sym x
weaken-tl₀ p (λ' {t₀} e) en en' x = ext λ x₁ → weaken-tl₀ (Super-cons p) e
                                                        (extend en t₀ x₁)
                                                        (extend en' t₀ x₁)
                                                        λ {t} {x₂} → extend-cons en en' x x₂
weaken-tl₀ p (e • e₁) en en' x = cong2 (λ f x₁ → f x₁) (weaken-tl₀ p e en en' x) (weaken-tl₀ p e₁ en en' x)
weaken-tl₀ p (pair e e₁) en en' x = cong2 _,_ (weaken-tl₀ p e en en' x) (weaken-tl₀ p e₁ en en' x)
weaken-tl₀ p (π₀ e) en en' x = cong fst (weaken-tl₀ p e en en' x)
weaken-tl₀ p (π₁ e) en en' x = cong snd (weaken-tl₀ p e en en' x)
weaken-tl₀ p (ι₀ e) en en' x = cong inl (weaken-tl₀ p e en en' x)
weaken-tl₀ p (ι₁ e) en en' x = cong inr (weaken-tl₀ p e en en' x)
weaken-tl₀ p (case e e₁ e₂) en en' x = cong3 caseOn (weaken-tl₀ p e en en' x) (weaken-tl₀ p e₁ en en' x) (weaken-tl₀ p e₂ en en' x)
weaken-tl₀ p (η e) en en' x = weaken-tl₀ p e en en' x
weaken-tl₀ p (up pr e) en en' x = weaken-tl₀ p e en en' x
weaken-tl₀ p (com e) en en' x = weaken-tl₀ p e en en' x
weaken-tl₀ p (μ e) en en' x = weaken-tl₀ p e en en' x
weaken-tl₀ p (fmap f e) en en' x = cong2 (λ f x₂ → f x₂) (weaken-tl₀ p f en en' x) (weaken-tl₀ p e en en' x)
weaken-tl₀ p <> en en' x = refl

fst-snd : ∀{A B : Set} {p : A × B} → p ≡ fst p , snd p
fst-snd {A} {B} {x , x₁} = refl

sem-bind* : ∀{Γ t₀ t₁ ℓ} → (p : ℓ ≼ t₁) → (e : Exp Γ (T ℓ t₀)) → (e₁ : Exp Γ (t₀ →' t₁)) → (en : env Γ)
          → ⟦ e ⟧ en ≡ ⟦ e ↓ ⟧₀ en  → ⟦ e₁ ⟧ en ≡ ⟦ e₁ ↓ ⟧₀ en
          → ⟦ e₁ ⟧ en (⟦ e ⟧ en) ≡ ⟦ bind* p (e ↓) (e₁ ↓) ⟧₀ en
sem-bind* (PFlow x₂) e e₁ en x x₁ = cong2 (λ f x₃ → f x₃) x₁ x
sem-bind* {t₁ = t₁} {ℓ = ℓ} (PInner p) e e₁ en x x₁ =
  let ih = sem-bind* p (Var hd) (λ' (Var hd)) (extend en (T ℓ _) (⟦ e₁ ⟧ en (⟦ e ⟧ en))) refl (ext λ z → refl) in
  let h₀ = cong (λ ex → ⟦ bind* p (Var hd) (λ' (Var hd)) ⟧₀ (extend en (T ℓ _) (ex (⟦ e ⟧ en)))) x₁ in
  let h₁ = cong (λ ex → ⟦ bind* p (Var hd) (λ' (Var hd)) ⟧₀ (extend en (T ℓ _) (⟦ e₁ ↓ ⟧₀ en ex))) x in
  trans ih (trans h₀ h₁)
sem-bind* {t₀ = t₀} (PProduct p p₁) e e₁ en x x₁ =
  let h₁ z = weaken-tl tl e₁ en (extend en t₀ z) λ {t} {x₂} → refl in
  let h₁₀ z = weaken-tl₀ tl (e₁ ↓) en (extend en t₀ z) λ {t} {x₂} → refl in
  let hlp₁ z = cong (λ f → f z) (sym (trans (trans (h₁₀ z) (sym x₁)) (sym (h₁ z)))) in
  let wkhlp₀ z = cong (λ e → fst (⟦ e ⟧₀ (extend en t₀ z) z)) (weaken↓ tl e₁) in
  let wkhlp₁ z = cong (λ e → snd (⟦ e ⟧₀ (extend en t₀ z) z)) (weaken↓ tl e₁) in
  let ih₁ = sem-bind* p e
              (λ' (π₁ (weaken tl e₁ • Var hd))) en x
              (ext λ z → trans (cong snd (hlp₁ z)) (sym (wkhlp₁ z)))
  in let ih₀ = sem-bind* p₁ e
              (λ' (π₀ (weaken tl e₁ • Var hd))) en x
              (ext λ z → trans (cong fst (hlp₁ z)) (sym (wkhlp₀ z)))
  in let hlp = cong2 _,_ ih₀ ih₁
  in let prs = fst-snd {p = ⟦ e₁ ⟧ en (⟦ e ⟧ en)}
  in let fsth = cong (λ ex → fst (ex (⟦ e ⟧ en))) (weaken-tl tl e₁ en (extend en t₀ (⟦ e ⟧ en)) λ {t} {x₂} → refl)
  in let sndh = cong (λ ex → snd (ex (⟦ e ⟧ en))) (weaken-tl tl e₁ en (extend en t₀ (⟦ e ⟧ en)) λ {t} {x₂} → refl)
  in let pairh = sym (cong2 _,_ fsth sndh)
  in let almost = trans (trans prs pairh) hlp
  in let hlp₂ = cong (λ ex → (⟦ bind* p₁ (e ↓) (λ' (π₀ (ex • Var hd))) ⟧₀ en , ⟦ bind* p (e ↓) (λ' (π₁ (ex • Var hd))) ⟧₀ en))
                     (weaken↓ tl e₁)
  in trans almost hlp₂
sem-bind* (PFunction {s = s} p) e e₁ en x x₁ =
  let hlp t₀ x z  = weaken-tl (λ z₁ → tl (tl z₁)) e₁ en (extend (extend en s z) t₀ x) λ {t} {x₂} → refl
  in let hlp₀ t₀ x z = weaken-tl₀ (λ z₁ → tl (tl z₁)) (e₁ ↓) en (extend (extend en s z) t₀ x) λ {t} {x₂} → refl
  in let ih z = sem-bind* p (weaken tl e)
                         (λ' ((weaken (λ z → tl (tl z)) e₁ • Var hd) • Var (tl hd)))
                         (extend en s z)
                         (trans (weaken-tl tl e en (extend en s z) λ {t} {x₂} → refl)
                         (trans (sym (weaken-tl tl e en (extend en s z) λ {t} {x₂} → refl))
                         (trans (weaken-tl tl e en (extend en s z) λ {t} {x₂} → refl)
                         (trans x (trans (sym (weaken-tl₀ tl (e ↓) en (extend en s z) λ {t} {x₂} → refl))
                         (cong (λ ex → ⟦ ex ⟧₀ (extend en s z)) (sym (weaken↓ tl e))))))))
                         (ext λ x₂ → trans (cong (λ f → f x₂ z) (hlp _ x₂ z))
                                    (trans (cong (λ f → f x₂ z) x₁)
                                    (trans (cong (λ f → f x₂ z) (sym (hlp₀ _ x₂ z)))
                                    (cong (λ ex → ⟦ ex ⟧₀ (extend (extend en s z) _ x₂) x₂ z)
                                          (sym (weaken↓ (λ z₁ → tl (tl z₁)) e₁)))
                         )))
  in ext λ x → trans (trans (cong2 (λ f x₂ → f x₂ x)
    (sym (weaken-tl (λ z → tl (tl z)) e₁ en (extend (extend en s x) _ (⟦ weaken (λ {x₂} → tl) e ⟧ (extend en s x))) λ {t} {x₂} → refl))
    (sym (weaken-tl tl e en (extend en s x) (λ {t} {x₂} → refl)))
    ) (ih x)) (cong2 (λ ex₀ ex₁ → ⟦ bind* p ex₀ (λ' ((ex₁ • Var hd) • Var (tl hd))) ⟧₀ (extend en s x)) 
                     (weaken↓ tl e)
                     (weaken↓ (λ {x₂} z → tl (tl z)) e₁))

sem↓ : ∀{Γ t} → (e : Exp Γ t) → (en : env Γ) → ⟦ e ⟧ en ≡ ⟦ e ↓ ⟧₀ en
sem↓ (Var x) en = refl
sem↓ (λ' e) en = ext λ z → sem↓ e (extend en _ z)
sem↓ (e • e₁) en = cong2 (λ f x → f x) (sem↓ e en) (sem↓ e₁ en)
sem↓ (pair e e₁) en = cong2 _,_ (sem↓ e en) (sem↓ e₁ en)
sem↓ (π₀ e) en = cong fst (sem↓ e en)
sem↓ (π₁ e) en = cong snd (sem↓ e en)
sem↓ (ι₀ e) en = cong inl (sem↓ e en)
sem↓ (ι₁ e) en = cong inr (sem↓ e en)
sem↓ (case e e₁ e₂) en = cong3 caseOn (sem↓ e en) (sem↓ e₁ en) (sem↓ e₂ en)
sem↓ (η e) en = sem↓ e en
sem↓ (bind x e e₁) en = sem-bind* x e e₁ en (sem↓ e en) (sem↓ e₁ en)
sem↓ <> en = refl

sem↑ : ∀{Γ t} → (e : Exp₀ Γ t) → (en : env Γ) → ⟦ e ⟧₀ en ≡ ⟦ e ↑ ⟧ en
sem↑ (Var x) en = refl
sem↑ (λ' e) en = ext λ z → sem↑ e (extend en _ z)
sem↑ (e • e₁) en = cong2 (λ f x → f x) (sem↑ e en) (sem↑ e₁ en)
sem↑ (pair e e₁) en = cong2 _,_ (sem↑ e en) (sem↑ e₁ en)
sem↑ (π₀ e) en = cong fst (sem↑ e en)
sem↑ (π₁ e) en = cong snd (sem↑ e en)
sem↑ (ι₀ e) en = cong inl (sem↑ e en)
sem↑ (ι₁ e) en = cong inr (sem↑ e en)
sem↑ (case e e₁ e₂) en = cong3 caseOn (sem↑ e en) (sem↑ e₁ en) (sem↑ e₂ en)
sem↑ (η e) en = sem↑ e en
sem↑ (μ e) en = sem↑ e en
sem↑ {t = t} (fmap {t = t'} e e₁) en =
  let ih = cong2 (λ f x → f x) (sem↑ e en) (sem↑ e₁ en) in
  let hlp = cong (λ ex → ex (⟦ e₁ ↑ ⟧ en)) (weaken-tl tl (e ↑) en (extend en t' (⟦ e₁ ↑ ⟧ en)) λ {t₁} {x} → refl) in
  trans ih (sym hlp)
sem↑ (up x e) en = sem↑ e en
sem↑ (com e) en = sem↑ e en
sem↑ <> en = refl
