module Uni where

{- This is a very very simplified bit of code to help me remind myself what the most basic kind of derivatives are like -}

open import Data.Fin
open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty

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

  
