/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Actions

/-!
# Additive universal property of balanced tensor products

Over the integer ground ring, balanced bilinear maps are balanced biadditive
maps. This file supplies an additive interface for the canonical Tau Ceti
carrier, including extensionality into arbitrary additive monoids.
-/

@[expose] public section

universe uR uM uN uA

namespace TauCeti.BalancedTensorProduct

variable {R : Type uR} {M : Type uM} {N : Type uN}
variable [Ring R] [AddCommGroup M] [AddCommGroup N]
variable [Module Rᵐᵒᵖ M] [Module R N]

scoped notation:100 m:100 " ⊗ᵇ[" R "] " n:101 => tmul ℤ R m n

/-- A biadditive map which is balanced over `R`. -/
structure BalancedAddMap (A : Type uA) [AddCommGroup A] where
  /-- The underlying function of a balanced map. It preserves zero and addition in each
  argument and satisfies `toFun (MulOpposite.op r • m) n = toFun m (r • n)`. -/
  toFun : M → N → A
  map_zero_left : ∀ n, toFun 0 n = 0
  map_add_left : ∀ m₁ m₂ n, toFun (m₁ + m₂) n = toFun m₁ n + toFun m₂ n
  map_zero_right : ∀ m, toFun m 0 = 0
  map_add_right : ∀ m n₁ n₂, toFun m (n₁ + n₂) = toFun m n₁ + toFun m n₂
  balance : ∀ (r : R) m n, toFun (MulOpposite.op r • m) n = toFun m (r • n)


namespace BalancedAddMap

variable {A : Type uA} [AddCommGroup A]

instance : CoeFun (BalancedAddMap (R := R) (M := M) (N := N) A) fun _ => M → N → A :=
  ⟨BalancedAddMap.toFun⟩

/-- A biadditive map is bilinear over the integers. -/
def toIntBilinear (b : BalancedAddMap (R := R) (M := M) (N := N) A) :
    M →ₗ[ℤ] N →ₗ[ℤ] A :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun m => AddMonoidHom.toIntLinearMap
        { toFun := b m
          map_zero' := b.map_zero_right m
          map_add' := b.map_add_right m }
      map_zero' := by ext n; exact b.map_zero_left n
      map_add' := by intro m m'; ext n; exact b.map_add_left m m' n }

end BalancedAddMap

/-- The additive lift of a balanced biadditive map on the canonical integer-based tensor. -/
def liftAddHom {A : Type uA} [AddCommGroup A]
    (b : BalancedAddMap (R := R) (M := M) (N := N) A) :
    TauCeti.BalancedTensorProduct ℤ R M N →+ A :=
  (lift b.toIntBilinear b.balance).toAddMonoidHom

@[simp]
theorem liftAddHom_tmul {A : Type uA} [AddCommGroup A]
    (b : BalancedAddMap (R := R) (M := M) (N := N) A) (m : M) (n : N) :
    liftAddHom b (tmul ℤ R m n) = b m n := by
  exact lift_tmul b.toIntBilinear b.balance m n

/-- Additive maps into arbitrary additive monoids are determined by pure tensors. -/
@[ext]
theorem addHom_ext {A : Type uA} [AddMonoid A]
    {g h : TauCeti.BalancedTensorProduct ℤ R M N →+ A}
    (H : ∀ m n, g (tmul ℤ R m n) = h (tmul ℤ R m n)) : g = h := by
  apply AddMonoidHom.ext
  intro z
  induction z using induction_on with
  | ht m n => exact H m n
  | ha x y hx hy => rw [map_add, map_add, hx, hy]

end TauCeti.BalancedTensorProduct
