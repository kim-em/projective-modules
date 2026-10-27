/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.LinearAlgebra.Dual.BaseChange

/-!
# Duals of finite projective modules and base change

This file proves that taking the dual of a finite projective module commutes
with arbitrary scalar extension. It generalizes `IsBaseChange.dual`, whose
mathlib statement assumes that the original module is finite free.
-/

@[expose] public section

open TensorProduct

namespace IsBaseChange

open Module LinearEquiv

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  {A : Type*} [CommSemiring A] [Algebra R A] [Module A W] [IsScalarTower R A W]
  {j : V →ₗ[R] W} (ibc : IsBaseChange A j)

variable [Module.Finite R V] [Projective R V]

/-- The dual of a supplied scalar extension, using canonical finite-projective evaluation. -/
noncomputable def toDualBaseChangeOfProjective :
    A ⊗[R] Dual R V ≃ₗ[A] Dual A W :=
  (TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := R) (A := A) (M := V)).trans
    (LinearEquiv.congrLeft A A ibc.equiv)

@[simp] theorem toDualBaseChangeOfProjective_tmul
    (a : A) (f : Dual R V) (v : V) :
    (toDualBaseChangeOfProjective ibc (a ⊗ₜ[R] f)) (j v) =
      a * algebraMap R A (f v) := by
  simp [toDualBaseChangeOfProjective, LinearEquiv.congrLeft,
    IsBaseChange.equiv_symm_apply, TauCeti.Module.Dual.baseChangeEvaluation_tmul]

@[simp] theorem toDualBaseChangeOfProjective_one_tmul (f : Dual R V) :
    toDualBaseChangeOfProjective ibc (1 ⊗ₜ[R] f) = ibc.toDual f := by
  apply LinearMap.ext
  intro w
  induction w using ibc.inductionOn with
  | tmul v => simp [toDual_comp_apply]
  | smul a w h => simp [h]
  | add x y hx hy => simp [hx, hy]

/-- Taking the dual of a finite projective module commutes with arbitrary
scalar extension. -/
theorem dual_of_projective : IsBaseChange A ibc.toDual := by
  apply of_equiv (toDualBaseChangeOfProjective ibc)
  intro f
  exact toDualBaseChangeOfProjective_one_tmul ibc f

end IsBaseChange
