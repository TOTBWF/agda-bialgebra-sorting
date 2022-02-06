
{-# OPTIONS --without-K #-}
module Sorting where

open import Level
open import Function

open import Data.Product using (Σ-syntax; _,_)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Bundles using (DecTotalOrder)
open import Relation.Binary.Structures using (IsDecTotalOrder)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Properties.DecTotalOrder as DecTotalᵖ

open ≡-Reasoning

-- Just assume funext for ease-of-use.
postulate
  funext : {S : Set}{T : S -> Set} {f g : (x : S) -> T x} -> ((x : S) -> f x ≡ g x) -> f ≡ g

--------------------------------------------------------------------------------
-- Preliminaries
--
-- To start, let's define initial algebras/terminal coalgebras.
-- This takes the place of explicit μ/ν types.

record Functor (F : Set → Set) : Set₁ where
  field
    map : {A B : Set} → (A → B) → F A → F B
    map-∘ : {A B C : Set} {f : A → B} {g : B → C} → ∀ x → (map g ∘ map f) x ≡ map (g ∘ f) x
    map-id : {A : Set} → ∀ (x : F A) → map id x ≡ x

--------------------------------------------------------------------------------
-- Initial Algebras + Terminal Coalgebras
--
-- We unpack everything here to make it a little less painful to deal with.

record InitialAlgebra {F : Set → Set} (F-Functor : Functor F) : Set₁ where
  open Functor F-Functor
  field
    Mu : Set
    In : F Mu → Mu
    fold : ∀ {A} → (F A → A) → Mu → A
    fold-commute : ∀ {A} (f : F A → A)
                   → fold f ∘ In ≡ f ∘ map (fold f)
    fold-unique : ∀ {A} {f : F A → A} → {h : Mu → A}
                  → h ∘ In ≡ f ∘ map h
                  → h ≡ fold f

  -- Lambek's Theorem.
  inᵒ : Mu → F Mu
  inᵒ = fold (map In)

  ⌈_⌉ : F Mu → Mu
  ⌈_⌉ = In

record TerminalCoalgebra {F : Set → Set} (F-Functor : Functor F) : Set₁ where
  open Functor F-Functor
  field
    Nu : Set
    Out : Nu → F Nu
    unfold : ∀ {A} → (A → F A) → A → Nu
    unfold-commute : ∀ {A} (f : A → F A)
                     → Out ∘ unfold f ≡ map (unfold f) ∘ f
    unfold-unique  : ∀ {A} {f : A → F A} → (h : A → Nu)
                     → Out ∘ unfold f ≡ map (unfold f) ∘ f
                     → h ≡ unfold f

  -- Lambek's Theorem.
  outᵒ : F Nu → Nu
  outᵒ = unfold (map Out)

  ⌊_⌋ : Nu → F Nu
  ⌊_⌋ = Out


record IsIso {A B : Set} (f : A → B) : Set where
  field
    inv : B → A
    isoˡ : ∀ x → inv (f x) ≡ x
    isoʳ : ∀ x → (f (inv x)) ≡ x

module _ {F : Set → Set} (F-Functor : Functor F)
         (μ : InitialAlgebra F-Functor) (ν : TerminalCoalgebra F-Functor) where

  open Functor F-Functor
  open InitialAlgebra μ
  open TerminalCoalgebra ν

  upcast : Mu → Nu
  upcast = unfold inᵒ

  -- Algebraic Compactness isn't something that has to happen!
  record AlgebraicallyCompact : Set where
    field
      compact : IsIso upcast

    open IsIso public using () renaming (inv to downcast)
    module compact = IsIso compact

data ListF (A : Set) (list : Set) : Set where
  nil : ListF A list
  cons : A → list → ListF A list

module _ where
  open Functor

  ListF-Functor : ∀ A → Functor (ListF A)
  map (ListF-Functor _) f nil = nil
  map (ListF-Functor A) f (cons k list) = cons k (f list)
  map-∘ (ListF-Functor A) nil = refl
  map-∘ (ListF-Functor A)  (cons _ _) = refl
  map-id (ListF-Functor A) nil = refl
  map-id (ListF-Functor A) (cons _ _) = refl

module Sort {A : Set} (_≤_ : A → A → Set) (order : IsDecTotalOrder _≡_ _≤_)
                  (μ : InitialAlgebra (ListF-Functor A)) (ν : TerminalCoalgebra (ListF-Functor A)) where

  open IsDecTotalOrder order using (_≤?_)
  open InitialAlgebra μ renaming (Mu to μList)
  open TerminalCoalgebra ν renaming (Nu to νList)
  open Functor (ListF-Functor A)

  bub : ListF A (ListF A μList) → ListF A μList
  bub nil = nil
  bub (cons x nil) = cons x (In nil)
  bub (cons x (cons y xs)) with x ≤? y
  ... | yes _ = cons x (In (cons y xs))
  ... | no  _ = cons y (In (cons x xs))

  bubbleSort : μList → νList
  bubbleSort = unfold (fold bub)

  naiveIns : ListF A νList → ListF A (ListF A νList)
  naiveIns nil = nil
  naiveIns (cons x xs) with ⌊ xs ⌋
  ... | nil = cons x nil
  ... | cons y xs with x ≤? y
  ...   | yes _ = cons x (cons y xs)
  ...   | no  _ = cons y (cons x xs)

  naiveInsertSort : μList → νList
  naiveInsertSort = fold (unfold naiveIns)

  swap : ∀ {list} → ListF A (ListF A list) → ListF A (ListF A list)
  swap nil = nil
  swap (cons x nil) = cons x nil
  swap (cons x (cons y xs)) with x ≤? y
  ...   | yes _ = cons x (cons y xs)
  ...   | no  _ = cons y (cons x xs)

  swap-natural : ∀ {R : Set} (f : ListF A R → ListF A R) → ∀ x → map f (swap x) ≡ swap (map f x)
  swap-natural f nil = refl
  swap-natural f (cons x nil) = {!!}
  swap-natural f (cons x (cons x₁ x₂)) = {!!}

  bub-swap : ∀ x → bub x ≡ map In (swap x)
  bub-swap nil = refl
  bub-swap (cons x nil) = refl
  bub-swap (cons x (cons y xs)) with x ≤? y
  ... | yes p = refl
  ... | no  p = refl

  ins-swap : ∀ x → naiveIns x ≡ swap (map Out x)
  ins-swap nil = refl
  ins-swap (cons x xs) with ⌊ xs ⌋
  ... | nil      = refl
  ... | cons y xs with x ≤? y
  ...   | yes p = refl
  ...   | no  p = refl

  bubbleSort′ : μList → νList
  bubbleSort′ = unfold (fold (map In ∘ swap))

  naiveInsertSort′ : μList → νList
  naiveInsertSort′ = fold (unfold (swap ∘ map Out))


  bubble′-commute : fold bub ∘ In ≡ map In ∘ swap ∘ map (fold bub)
  bubble′-commute = begin
      fold bub ∘ In
    ≡⟨ fold-commute bub ⟩
      bub ∘ map (fold bub)
    ≡⟨ cong (λ ϕ → ϕ ∘ map (fold bub)) (funext bub-swap) ⟩
      map In ∘ swap ∘ map (fold bub)
    ∎

  naiveInsert′-commute : Out ∘ unfold naiveIns ≡ map (unfold naiveIns) ∘ swap ∘ map Out
  naiveInsert′-commute = begin
      Out ∘ unfold naiveIns
    ≡⟨ unfold-commute naiveIns ⟩
      map (unfold naiveIns) ∘ naiveIns
    ≡⟨ cong (λ ϕ → map (unfold naiveIns) ∘ ϕ) (funext ins-swap) ⟩
      map (unfold naiveIns) ∘ swap ∘ map Out
    ∎

record Bialgebra {F G : Set → Set} (F-Functor : Functor F) (G-Functor : Functor G) : Set₁ where
  private
    module F = Functor F-Functor
    module G = Functor G-Functor
  field
    X : Set
    reduce : F X → X
    expand : X → G X
    swap : F (G X) → G (F X)
    distrib :  expand ∘ reduce ≡ G.map reduce ∘ swap ∘ F.map expand 

module _ {F G : Set → Set} {F-Functor : Functor F} {G-Functor : Functor G} where
  private
    module F = Functor F-Functor
    module G = Functor G-Functor
  
  record BialgebraMorphism (α β : Bialgebra F-Functor G-Functor) : Set₁ where
    private
      module α = Bialgebra α
      module β = Bialgebra β

    field
      to : α.X → β.X
      reduce-commute : to ∘ α.reduce ≡ β.reduce ∘ F.map to
      expand-commute : G.map to ∘ α.expand ≡ β.expand ∘ to
  

module SortBialgebra {A : Set} (_≤_ : A → A → Set) (order : IsDecTotalOrder _≡_ _≤_)
                     (μ : InitialAlgebra (ListF-Functor A)) (ν : TerminalCoalgebra (ListF-Functor A)) where

  open IsDecTotalOrder order using (_≤?_)
  open InitialAlgebra μ renaming (Mu to μList)
  open TerminalCoalgebra ν renaming (Nu to νList)
  open Functor (ListF-Functor A)
  open Bialgebra
  open BialgebraMorphism
  open Sort _≤_ order μ ν renaming (swap to swap′)

  bubble-bialgebra : Bialgebra (ListF-Functor A) (ListF-Functor A)
  X bubble-bialgebra = μList
  reduce bubble-bialgebra = In
  expand bubble-bialgebra = fold bub
  swap bubble-bialgebra = swap′
  distrib bubble-bialgebra = bubble′-commute

  insert-bialgebra : Bialgebra (ListF-Functor A) (ListF-Functor A)
  X insert-bialgebra = νList
  reduce insert-bialgebra = unfold naiveIns
  expand insert-bialgebra = Out
  swap insert-bialgebra = swap′
  distrib insert-bialgebra = naiveInsert′-commute

  fold-bialgebra : Bialgebra (ListF-Functor A) (ListF-Functor A)
  X fold-bialgebra = μList
  reduce fold-bialgebra = In
  expand fold-bialgebra = fold (map In ∘ swap′)
  swap fold-bialgebra = swap′
  distrib fold-bialgebra = fold-commute (map In ∘ swap′)

  fold-initial : ∀ (α : Bialgebra (ListF-Functor A) (ListF-Functor A)) → BialgebraMorphism fold-bialgebra α
  to (fold-initial α) = fold (reduce α)
  reduce-commute (fold-initial α) = fold-commute (reduce α)
  expand-commute (fold-initial α) = begin
      map (fold (reduce α)) ∘ fold (map In ∘ swap′)
    ≡⟨ fold-unique lemma ⟩
      fold (map (reduce α) ∘ swap′)
    ≡˘⟨ fold-unique lemma′ ⟩
      expand α ∘ fold (reduce α)
    ∎
    where
      lemma : map (fold (reduce α)) ∘ fold (map In ∘ swap′) ∘ In ≡
               map (reduce α) ∘ swap′ ∘ map (map (fold (reduce α)) ∘ fold (map In ∘ swap′))
      lemma = begin
          map (fold (reduce α)) ∘ fold (map In ∘ swap′) ∘ In
        ≡⟨ cong (λ ϕ → map (fold (reduce α)) ∘ ϕ) (fold-commute (λ x → map In (swap′ x))) ⟩
          map (fold (reduce α)) ∘ map In ∘ swap′ ∘ map (fold (map In ∘ swap′))
        ≡⟨ cong (λ ϕ → ϕ ∘ swap′ ∘ map (fold (map In ∘ swap′))) (funext map-∘) ⟩
          map (fold (reduce α) ∘ In) ∘ swap′ ∘ map (fold (map In ∘ swap′))
        ≡⟨ cong (λ ϕ → map ϕ ∘ swap′ ∘ map (fold (map In ∘ swap′))) (fold-commute (reduce α)) ⟩
          map (reduce α ∘ map (fold (reduce α))) ∘ swap′ ∘ map (fold (map In ∘ swap′))
        ≡˘⟨ cong (λ ϕ → ϕ ∘ swap′ ∘ map (fold (map In ∘ swap′))) (funext map-∘) ⟩
          map (reduce α) ∘ map (map (fold (reduce α))) ∘ swap′ ∘ map (fold (map In ∘ swap′))
        ≡⟨ {!!} ⟩
          map (reduce α) ∘ swap′ ∘ map (map (fold (reduce α)) ∘ fold (map In ∘ swap′))
        ∎

      lemma′ : expand α ∘ fold (reduce α) ∘ In ≡ map (reduce α) ∘ swap′ ∘ map (expand α ∘ fold (reduce α))
      lemma′ = begin
          expand α ∘ fold (reduce α) ∘ In
        ≡⟨ cong (λ ϕ → expand α ∘ ϕ) (fold-commute (reduce α)) ⟩
          expand α ∘ reduce α ∘ map (fold (reduce α))
        ≡⟨ cong (λ ϕ → ϕ ∘ map (fold (reduce α))) (distrib α) ⟩
          map (reduce α) ∘ swap α ∘ map (expand α) ∘ map (fold (reduce α))
        ≡⟨ {!!} ⟩
          map (reduce α) ∘ swap′ ∘ map (expand α ∘ fold (reduce α))
        ∎

module DisplayedSort {A : Set} (_≤_ : A → A → Set) (is-order : IsDecTotalOrder _≡_ _≤_)
                  (μ : InitialAlgebra (ListF-Functor A)) (ν : TerminalCoalgebra (ListF-Functor A)) where

  open IsDecTotalOrder is-order using (_≤?_; total)
   
  order : DecTotalOrder 0ℓ 0ℓ 0ℓ
  order = record
    { Carrier = A
    ; _≈_ = _≡_
    ; _≤_ = _≤_
    ; isDecTotalOrder = is-order
    }

  open DecTotalᵖ order
  open InitialAlgebra μ renaming (Mu to μList)
  open TerminalCoalgebra ν renaming (Nu to νList)
  open Functor (ListF-Functor A)

  data Ordered {list : Set} : (ListF A (ListF A list)) → Set where
    nil-ordered    : Ordered nil
    single-ordered : ∀ {x} → Ordered (cons x nil)
    cons-ordered   : ∀ {x y xs} → x ≤ y → Ordered (cons x (cons y xs))

  swap : ∀ {list} → ListF A (ListF A list) → ListF A (ListF A list)
  swap nil = nil
  swap (cons x nil) = (cons x nil)
  swap (cons x (cons y xs)) with x ≤? y
  ...   | yes x≤y  = cons x (cons y xs)
  ...   | no  ¬x≤y = cons y (cons x xs)

  swap-ordered : ∀ {list} → (xs : ListF A (ListF A list)) → Ordered (swap xs)
  swap-ordered nil = nil-ordered
  swap-ordered (cons x nil) = single-ordered
  swap-ordered (cons x (cons y xs)) with x ≤? y
  ...   | yes x≤y  = cons-ordered x≤y
  ...   | no  ¬x≤y = cons-ordered (≰⇒≥ ¬x≤y)

  bubbleSort : μList → νList
  bubbleSort = unfold (fold (map In ∘ swap))

-- These should be slices over some F-Algebra...
-- IE,
record Algebra {F : Set → Set} (F-Functor : Functor F) : Set₁ where
  field
    X : Set
    eval : F X → X

record AlgebraMorphism {F : Set → Set} {F-Functor : Functor F} (α β : Algebra F-Functor) : Set₁ where
  open Functor F-Functor
  private
    module α = Algebra α
    module β = Algebra β
  field
    to : α.X → β.X
    commute : to ∘ α.eval ≡ β.eval ∘ map to 

record DisplayedAlgebra {F : Set → Set} {F-Functor : Functor F} (γ : Algebra F-Functor) : Set₁ where
  open Functor F-Functor
  field
    δ : Algebra F-Functor
    prove : AlgebraMorphism δ γ
