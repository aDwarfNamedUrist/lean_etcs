class ETCS where
  Set : Type
  Hom : Set → Set → Type
  comp : {a b c : Set} → Hom a b → Hom b c → Hom a c
  id : {a : Set} → Hom a a
  id_left : ∀ a b (f : Hom a b), comp id f = f
  id_right : ∀ a b (f : Hom a b), comp f id = f
  one : Set
  term_mor : (a : Set) → Hom a one
  one_terminal : ∀ x f, term_mor x = f
  pullback : {a b c : Set} → (f : Hom a c) → (g : Hom b c) →
    ((d : Set) × (Hom d a) × (Hom d b))
  pullback_comm : ∀ a b c (f : Hom a c) (g : Hom b c),
    comp (pullback f g).2.1 f = comp (pullback f g).2.2 g
  pullback_univ : ∀ a b c x (f : Hom a c) (g : Hom b c) (h₁ : Hom x a) (h₂ : Hom x b),
    comp h₁ f = comp h₂ g → ∃ h : Hom x (pullback f g).1,
    comp h (pullback f g).2.1 = h₁ ∧ comp h (pullback f g).2.2 = h₂
  powerset : Set → Set
  elem : Set → Set
  lambda : {x : Set} → Hom (elem x) (powerset x)
  rho : {x : Set} → Hom (elem x) x
  power_joint_monic : ∀ a x (h i : Hom x (elem a)),
    comp h lambda = comp i lambda ∧ comp h rho = comp i rho
     → h = i
  power_univ : ∀ c d r (f : Hom r c) (g : Hom r d),
    (∀ x (h i : Hom x r), comp h f = comp i f ∧ comp h g = comp i g) →
    ∃ (rel : Hom r (elem c)) (χ : Hom d (powerset c)), comp rel rho = f ∧
    ∀ x (h₁ : Hom x (elem c)) (h₂ : Hom x d), comp h₁ lambda = comp h₂ χ →
    ∃ h : Hom x r, comp h rel = h₁ ∧ comp h g = h₂
  nat : Set
  nat_zero : Hom one nat
  nat_succ : Hom nat nat
  nat_rec_exists : ∀ a (x : Hom one a) (f : Hom a a), ∃ r : Hom nat a,
    comp zero r = x ∧ comp succ r = comp r f
  nat_rec_uniqe : ∀ a (f g : Hom nat a), 
    comp nat_zero f = comp nat_zero g ∧
    comp nat_succ f = comp nat_succ g → f = g 
  well_founded : ∀ a b (f g : Hom a b), 
    (∀ h : Hom one a, comp h f = comp h g) → f = g
  ax_choice : ∀ a b (f : Hom a b), 
    (∀ x (g₁ g₂ : Hom b x), comp f g₁ = comp f g₂ → g₁ = g₂) → 
    ∃ (i : Hom b a), comp i f = id
variable [ETCS]
open ETCS
