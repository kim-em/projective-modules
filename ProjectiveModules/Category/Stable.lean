/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents (stable-category contribution); see docs/CREDITS.md
module

public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Detecting stable module morphisms by Ext

The stable quotient and projective-factorization predicate are supplied by Tau Ceti.
This file proves the additional characterization of projective factorizations by
precomposition on all first Ext groups, with independent ring and module universes.
-/

@[expose] public section

universe uR uM

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace ModuleCat

variable {R : Type uR} [Ring R]

/-- A morphism factors through a projective module exactly when it acts by zero on every first
`Ext` group by precomposition. -/
lemma projectiveFactorsThrough_iff_ext_one_precomp_eq_zero [Small.{uM} R]
    {M N : ModuleCat.{uM} R} (f : M ⟶ N) :
    (TauCeti.ExactStructure.abelian (ModuleCat.{uM} R)).isProjective.FactorsThrough f ↔
      ∀ (A : ModuleCat.{uM} R),
        (Ext.mk₀ f).precomp A (zero_add 1) = 0 := by
  rw [CategoryTheory.ObjectProperty.factorsThrough_iff]
  constructor
  · rintro ⟨P, hP, i, p, rfl⟩ A
    let _ : CategoryTheory.Projective P :=
      (TauCeti.ExactStructure.abelian_isProjective_iff P).mp hP
    ext e
    change (Ext.mk₀ (i ≫ p)).comp e (zero_add 1) = 0
    rw [← Ext.mk₀_comp_mk₀_assoc]
    rw [Ext.eq_zero_of_projective ((Ext.mk₀ p).comp e (zero_add 1))]
    simp
  · intro h
    let P : ModuleCat.{uM} R := CategoryTheory.Projective.over N
    let p : P ⟶ N := CategoryTheory.Projective.π N
    let S : ShortComplex (ModuleCat.{uM} R) :=
      ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel S (kernelIsKernel p) }
    have hf : (Ext.mk₀ f).comp hS.extClass (zero_add 1) = 0 := by
      have hf' := DFunLike.congr_fun (h (kernel p)) hS.extClass
      exact hf'
    obtain ⟨e, he⟩ := Ext.covariant_sequence_exact₃ M hS (Ext.mk₀ f) rfl hf
    refine ⟨P, (TauCeti.ExactStructure.abelian_isProjective_iff P).mpr inferInstance,
      Ext.addEquiv₀ e, p, ?_⟩
    apply (Ext.mk₀_bijective _ _).1
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
    exact he.symm

/-- Two module morphisms have the same effect by precomposition on all first `Ext` groups exactly
when their difference factors through a projective module. -/
lemma projectiveFactorsThrough_sub_iff_ext_one_precomp_eq [Small.{uM} R]
    {M N : ModuleCat.{uM} R} (f g : M ⟶ N) :
    (TauCeti.ExactStructure.abelian (ModuleCat.{uM} R)).isProjective.FactorsThrough (f - g) ↔
      ∀ (A : ModuleCat.{uM} R),
        (Ext.mk₀ f).precomp A (zero_add 1) =
          (Ext.mk₀ g).precomp A (zero_add 1) := by
  rw [projectiveFactorsThrough_iff_ext_one_precomp_eq_zero]
  constructor
  · intro h A
    ext e
    have he := DFunLike.congr_fun (h A) e
    change (Ext.mk₀ f).comp e (zero_add 1) = (Ext.mk₀ g).comp e (zero_add 1)
    have hmk : Ext.mk₀ (f - g) = Ext.mk₀ f - Ext.mk₀ g := by
      rw [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, sub_eq_add_neg]
    change (Ext.mk₀ (f - g)).comp e (zero_add 1) = 0 at he
    rw [hmk, sub_eq_add_neg, Ext.add_comp, Ext.neg_comp] at he
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using he)
  · intro h A
    ext e
    have he := DFunLike.congr_fun (h A) e
    change (Ext.mk₀ f).comp e (zero_add 1) = (Ext.mk₀ g).comp e (zero_add 1) at he
    change (Ext.mk₀ (f - g)).comp e (zero_add 1) = 0
    rw [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.add_comp, Ext.neg_comp]
    simpa only [sub_eq_add_neg] using (sub_eq_zero.mpr he)

end ModuleCat
