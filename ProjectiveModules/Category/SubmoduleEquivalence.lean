/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Equivalence
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Submodule lattices under module-category equivalences

An ordinary equivalence between categories of left modules induces an order
isomorphism between their lattices of submodules. Its forward map is the range
of the image of a submodule inclusion. Its inverse map uses the inverse functor
and the inverse of the unit isomorphism to return to the original module.

The scalar and carrier universes are independent. The rings need not be
commutative, and no additive or linear structure on the equivalence is assumed.
The identity and composition laws describe the coherence of this transport.

## References

The construction uses Mathlib's module-subobject correspondence by Markus Himmel,
subobject equivalences by Bhavik Mehta and Kim Morrison, and the equivalence/order
isomorphism API by Stephen Morgan, Kim Morrison, Johannes Hölzl and Reid Barton.
Tau Ceti supplies `CategoryTheory.Equivalence.submoduleOrderIso`; this file records
its inverse and coherence laws.
-/

@[expose] public section

universe uR uS uT vR vS vT

open CategoryTheory

namespace CategoryTheory.Equivalence

open ModuleCat

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

private theorem submoduleOrderIso_range
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) {X Y : ModuleCat.{vR} R}
    (i : Y ⟶ X) [Mono i] :
    submoduleOrderIso e X (LinearMap.range i.hom) =
      LinearMap.range (e.functor.map i).hom := by
  have hi : ofHom i.hom.rangeRestrict ≫ ofHom (LinearMap.range i.hom).subtype = i := by
    ext x
    rfl
  rw [submoduleOrderIso_apply]
  have : Epi (ofHom i.hom.rangeRestrict) :=
    (ModuleCat.epi_iff_surjective _).mpr i.hom.surjective_rangeRestrict
  calc
    _ = LinearMap.range (e.functor.map (ofHom i.hom.rangeRestrict) ≫
        e.functor.map (ofHom (LinearMap.range i.hom).subtype)).hom := by
      rw [ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top _
        (ModuleCat.range_eq_top_of_epi _)]
    _ = _ := by rw [← e.functor.map_comp, hi]

/-- Inverse transport applies the inverse functor to the inclusion and then uses
 the inverse unit isomorphism to land in the original module. -/
@[simp]
theorem submoduleOrderIso_symm_apply
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) (X : ModuleCat.{vR} R)
    (P : Submodule S (e.functor.obj X)) :
    (submoduleOrderIso e X).symm P =
      LinearMap.range
        ((e.inverse.map (ofHom P.subtype) ≫ (e.unitIso.app X).inv).hom) := by
  apply (e.submoduleOrderIso X).injective
  rw [OrderIso.apply_symm_apply, submoduleOrderIso_range]
  have h : e.functor.map (e.inverse.map (ofHom P.subtype) ≫ (e.unitIso.app X).inv) =
      (e.counitIso.app (ModuleCat.of S P)).hom ≫ ofHom P.subtype := by
    rw [Functor.map_comp]
    have hu : e.functor.map (e.unitIso.app X).inv =
        (e.counitIso.app (e.functor.obj X)).hom := by
      exact (e.counit_app_functor X).symm
    rw [hu]
    exact e.counitIso.hom.naturality (ofHom P.subtype)
  rw [h, ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top _
    (ModuleCat.range_eq_top_of_epi _)]
  exact (Submodule.range_subtype P).symm

/-- Transport along the identity equivalence is the identity on submodules. -/
@[simp]
theorem submoduleOrderIso_refl (X : ModuleCat.{vR} R) :
    submoduleOrderIso (CategoryTheory.Equivalence.refl (C := ModuleCat.{vR} R)) X =
      OrderIso.refl (Submodule R X) := by
  apply OrderIso.ext
  funext N
  rw [submoduleOrderIso_apply]
  exact Submodule.range_subtype N

/-- Transport along a composite equivalence is the composite of the two
submodule order isomorphisms, with an independent third ring and carrier universe. -/
theorem submoduleOrderIso_trans
    {T : Type uT} [Ring T]
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S)
    (f : ModuleCat.{vS} S ≌ ModuleCat.{vT} T) (X : ModuleCat.{vR} R) :
    submoduleOrderIso (e.trans f) X =
      (submoduleOrderIso e X).trans
        (submoduleOrderIso f (e.functor.obj X)) := by
  apply OrderIso.ext
  funext N
  change submoduleOrderIso (e.trans f) X N =
    submoduleOrderIso f (e.functor.obj X)
      (submoduleOrderIso e X N)
  rw [submoduleOrderIso_apply (e.trans f),
    submoduleOrderIso_apply e]
  exact (submoduleOrderIso_range f
    (e.functor.map (ofHom N.subtype))).symm

end CategoryTheory.Equivalence
