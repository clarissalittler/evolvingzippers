module Uni where

{- This is a very very simplified bit of code to help me remind myself what the most basic kind of derivatives are like -}

open import Data.Fin
open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.List

module Try1 where

  data U (n : ℕ) : Set where
    _×'_ : U n -> U n -> U n
    _+'_ : U n -> U n -> U n
    1' : U n
    0' : U n
    Var : Fin n -> U n

  aux-∂ : {n : ℕ} -> Fin n -> Fin n -> Bool 
  aux-∂ zero zero = true
  aux-∂ zero (suc v2) = false
  aux-∂ (suc v1) zero = false
  aux-∂ (suc v1) (suc v2) = aux-∂ v1 v2
  
  boolToU : {n : ℕ} -> Bool -> U n
  boolToU true = 1'
  boolToU false = 0'

  ∂ : {n : ℕ} -> Fin n -> U n -> U n
  ∂ v (u ×' u₁) = (∂ v u ×' u₁) +' (u ×' ∂ v u₁)
  ∂ v (u +' u₁) = ∂ v u +' ∂ v u₁
  ∂ v 1' = 0'
  ∂ v 0' = 0'
  ∂ v (Var x) = boolToU (aux-∂ v x)

  ⟦_⟧ : {n : ℕ} -> U n -> (Fin n -> Set) -> Set
  ⟦_⟧ (u ×' u₁) γ = ⟦ u ⟧ γ × ⟦ u₁ ⟧ γ
  ⟦_⟧ (u +' u₁) γ = ⟦ u ⟧ γ ⊎ ⟦ u₁ ⟧ γ
  ⟦_⟧ 1' γ = ⊤
  ⟦_⟧ 0' γ = ⊥
  ⟦_⟧ (Var x) γ = γ x 

module Try2 where
  
  data U : Set where
    _×'_ : U -> U -> U
    _+'_ : U -> U -> U
    1' : U
    0' : U
    Var : U

  ⟦_⟧ : U -> Set -> Set
  ⟦_⟧ (u ×' u₁) A = ⟦ u ⟧ A × ⟦ u₁ ⟧ A
  ⟦_⟧ (u +' u₁) A = ⟦ u ⟧ A ⊎ ⟦ u₁ ⟧ A
  ⟦_⟧ 1' A = ⊤
  ⟦_⟧ 0' A = ⊥
  ⟦_⟧ Var A = A
 
  δ : U -> U
  δ (u ×' u₁) = (δ u ×' u₁) +' (u ×' δ u₁)
  δ (u +' u₁) = (δ u) +' (δ u₁)
  δ 1' = 0'
  δ 0' = 0'
  δ Var = 1'

  data Mu (A : U) : Set where
    cons : ⟦ A ⟧ (Mu A) -> Mu A
 
  natU : U
  natU = 1' +' Var

  nat : Set
  nat = Mu natU

  zU : nat
  zU = cons (inj₁ tt)

  sU : nat -> nat
  sU n = cons (inj₂ n)

  natZU : U
  natZU = δ natU

  natZ : Set
  natZ = Mu natZU

  blah : natZ
  blah = cons (inj₂ tt)

  zipper : U -> Set
  zipper D = (List (Mu (δ D))) × (Mu D)

-- durrr, do I need to do this from the "inside" of the recursion? Like what's the deal here?
  rebuild : (D : U) -> zipper D -> Mu D
  rebuild (d ×' d₁) z = {!!}
  rebuild (d +' d₁) (proj₁ , proj₂) = {!!}
  rebuild 1' ([] , cons tt) = cons tt
  rebuild 1' (cons () ∷ xs , cons tt) 
  rebuild 0' (proj₁ , cons ())
  rebuild Var (proj₁ , proj₂) = {!!}

  rebuild' : (A : U) -> Mu (δ A) -> Mu A -> Mu A
  rebuild' (A ×' A₁) z (cons (proj₁ , proj₂)) = {!!}
  rebuild' (A +' A₁) (cons (inj₁ x)) (cons (inj₁ x₁)) = {!!}
  rebuild' (A +' A₁) (cons (inj₁ x)) (cons (inj₂ y)) = {!!}
  rebuild' (A +' A₁) (cons (inj₂ y)) a = {!!}
  rebuild' 1' (cons ()) a -- graghle these simple cases are working the way I want but...
  rebuild' 0' (cons ()) a -- essentially there's some ugliness with the recursion that I'm not liking
  rebuild' Var d a = cons a --- maybe I need to take the δ on the fixed point? So I notice in a really old
                            -- conor paper that he has the μ as an explicit code in the universe and uses partial derivatives, maybe go back to that 

module Try3 where
  
  data U (n : ℕ) : Set where
    _×'_ : U n -> U n -> U n
    _+'_ : U n -> U n -> U n
    1' : U n
    0' : U n
    Var : Fin n -> U n
    μ : U (suc n) -> U n

  emptyEnv : Fin 0 -> Set
  emptyEnv () -- god I love proper pattern matching. I suppose I could just use Vec Set n tho

  ⟦_⟧_ : {n : ℕ} -> U n -> (Fin n -> Set) -> Set
  ⟦ u ×' u₁ ⟧ γ = ⟦ u ⟧ γ × ⟦ u₁ ⟧ γ
  ⟦ u +' u₁ ⟧ γ = {!!}
  ⟦ 1' ⟧ γ = ⊤
  ⟦ 0' ⟧ γ = ⊥
  ⟦ Var x ⟧ γ = γ x
  ⟦ μ u ⟧ γ = {!!} -- oohhhhh this is why I should use vec or something not Fin n wompwomp, well fix that later okay

  ∂ : {n : ℕ} -> Fin n -> U n -> U n
  ∂ y (u ×' u₁) = {!!}
  ∂ y (u +' u₁) = ∂ y u +' ∂ y u₁
  ∂ y 1' = 0'
  ∂ y 0' = 0'
  ∂ y (Var x) = {!!}
  ∂ y (μ u) = {!!}
