/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.Category.FiniteProjectiveSmallness
public import TauCeti.CategoryTheory.GrothendieckGroup.Split
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.LinearAlgebra.StdBasis

/-!
# K₀ of finite projective right modules

For an arbitrary ring `R`, `KTheory.ProjectiveClass R` is the ring-sized
commutative monoid of isomorphism classes of finitely generated projective
right `R`-modules. Its zero is the zero module and its addition is binary
direct sum, modeled by the product of module carriers.

`KTheory.K0 R` is the additive Grothendieck group of this monoid. The maps
`ProjectiveClass.of` and `K0.of` accept modules in arbitrary carrier universes:
the ring-universe representatives of `ModuleCat.FiniteProjective` place them
in one reference category. Equality in `ProjectiveClass R` is module
isomorphism; equality in `K0 R` need not be module isomorphism.
`ProjectiveClass.liftFunction` descends isomorphism-invariant functions from the
reference modules to functions on their classes. `ProjectiveClass.lift` bundles
this descent as an additive map when the function preserves zero and direct sum.

## Implementation notes

Tau Ceti's `ObjectCode` supplies the small additive monoid of isomorphism
classes under binary biproduct. The ordinary product of module carriers is
compared with this categorical biproduct explicitly. Mathlib's group completion
of this monoid is canonically identified with Tau Ceti's `SplitK0` by
`K0.splitK0Equiv`. Representatives accept independent carrier universes.

## References and credits

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*,
  Chapter II, group completion and the definition of K₀.
* Mathlib's skeleton, chosen finite-product Cartesian monoidal structure,
  algebraic transport to `Shrink`, and additive Grothendieck group.
* Mathlib's finite-coordinate linear equivalence and free-module instances.
* The finite-projective category and representative formalization in this
  library, and Formal Frontier's Algebraic Direct Limits object-class
  group-completion formalization, whose skeleton-based approach this file
  follows without importing a separate completion framework.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace KTheory

variable (R : Type u) [Ring R]

/-- Direct-sum classes of finite projective right modules, using Tau Ceti's
canonical small monoid of object codes. -/
noncomputable def ProjectiveClass : Type u :=
  TauCeti.ObjectCode.{u} (ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ)

/-- Use the canonical object-code addition without exposing the categorical
carrier to recursive algebraic instance search. -/
noncomputable instance : AddCommMonoid (ProjectiveClass R) :=
  TauCeti.instAddCommMonoidObjectCode (C := ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ)

namespace ProjectiveClass

variable (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]

/-- The direct-sum isomorphism class of a finite projective right module,
using its ring-universe representative. -/
@[no_expose] noncomputable def of : ProjectiveClass R :=
  TauCeti.objectCode (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M)

/-- Two classes, including inputs in different carrier universes, are equal
exactly when the right modules are linearly equivalent. -/
theorem of_eq_iff (N : Type w) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    of R M = of R N ↔ Nonempty (M ≃ₗ[Rᵐᵒᵖ] N) := by
  change TauCeti.objectCode (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M) =
    TauCeti.objectCode (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ N) ↔ _
  exact ModuleCat.FiniteProjective.objectCode_repr_eq_iff Rᵐᵒᵖ M N

/-- Linear equivalence preserves the direct-sum isomorphism class. -/
theorem of_eq_of_equiv {N : Type w} [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] (e : M ≃ₗ[Rᵐᵒᵖ] N) :
    of R M = of R N :=
  (of_eq_iff R M N).2 ⟨e⟩

/-- Passing to the ring-universe representative does not change the class. -/
@[simp↓]
theorem of_repr : of R (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M) = of R M :=
  of_eq_of_equiv R _ (ModuleCat.FiniteProjective.reprEquiv Rᵐᵒᵖ M)

/-- Passing to the finite-module representative does not change the projective class. -/
@[simp]
theorem of_finite_repr :
    @of R _ (Module.Finite.repr Rᵐᵒᵖ M) _ _ _
      (Module.Projective.of_equiv' (Module.Finite.reprEquiv Rᵐᵒᵖ M).symm) = of R M :=
  of_repr R M

/-- A carrier lift does not change the isomorphism class. -/
@[simp]
theorem of_ulift : of R (ULift.{w} M) = of R M := by
  exact of_eq_of_equiv R _ ULift.moduleEquiv

/-- The class of any zero module is the monoid zero, including over the zero ring. -/
@[simp]
theorem of_zero (Z : Type v) [AddCommGroup Z] [Module Rᵐᵒᵖ Z] [Subsingleton Z] :
    of R Z = 0 := by
  change TauCeti.objectCode (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ Z) =
    (0 : TauCeti.ObjectCode.{u} (ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ))
  rw [← TauCeti.objectCode_zero]
  apply TauCeti.objectCode_congr
  exact (ModuleCat.FiniteProjective.reprZeroIso Rᵐᵒᵖ Z).trans
    (IsZero.isoZero (IsZero.of_full_of_faithful_of_isZero
      (ModuleCat.isFiniteProjective Rᵐᵒᵖ).ι _
      (ModuleCat.isZero_iff_subsingleton.mpr (by
        change Subsingleton PUnit.{u + 1}
        infer_instance))))

/-- Binary direct sum of modules computes addition of isomorphism classes. -/
@[simp]
theorem of_prod (N : Type w) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    of R (M × N) = of R M + of R N := by
  change TauCeti.objectCode (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ (M × N)) =
    (TauCeti.objectCode (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M) +
      TauCeti.objectCode (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ N) :
        TauCeti.ObjectCode.{u} (ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ))
  rw [← TauCeti.objectCode_biprod]
  apply TauCeti.objectCode_congr
  refine (ModuleCat.FiniteProjective.reprProdIso Rᵐᵒᵖ M N).trans ?_
  let X := ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M
  let Y := ModuleCat.FiniteProjective.repr Rᵐᵒᵖ N
  let cone : BinaryFan X Y := BinaryFan.mk
    ((ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ
      (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y)) X).symm (LinearMap.fst Rᵐᵒᵖ X Y))
    ((ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ
      (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y)) Y).symm (LinearMap.snd Rᵐᵒᵖ X Y))
  let hcone : IsLimit cone := BinaryFan.IsLimit.mk _
    (fun {T} f g ↦ (ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ T _).symm
      ((ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ T X f).prod
        (ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ T Y g)))
    (fun _ _ ↦ by apply ModuleCat.FiniteProjective.hom_ext; rfl)
    (fun _ _ ↦ by apply ModuleCat.FiniteProjective.hom_ext; rfl)
    (fun {T} f g m hf hg ↦ by
      apply ModuleCat.FiniteProjective.hom_ext
      apply LinearMap.ext
      intro x
      exact Prod.ext
        (congrArg (fun h : T ⟶ X ↦
          ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ T X h x) hf)
        (congrArg (fun h : T ⟶ Y ↦
          ModuleCat.FiniteProjective.homLinearEquiv Rᵐᵒᵖ T Y h x) hg))
  exact hcone.conePointUniqueUpToIso (BinaryBiproduct.isLimit X Y)

/-- The finite coordinate module has the class of `n` copies of the regular
right module, for arbitrary rings. -/
@[simp]
theorem of_fin_fun_eq_nsmul (n : ℕ) :
    of R (Fin n → Rᵐᵒᵖ) = n • of R Rᵐᵒᵖ := by
  induction n with
  | zero => simp only [of_zero, zero_nsmul]
  | succ n ih =>
    calc
      of R (Fin (n + 1) → Rᵐᵒᵖ) = of R (Rᵐᵒᵖ × (Fin n → Rᵐᵒᵖ)) :=
        of_eq_of_equiv R _
          (Fin.consLinearEquiv Rᵐᵒᵖ (fun _ : Fin (n + 1) ↦ Rᵐᵒᵖ)).symm
      _ = of R Rᵐᵒᵖ + of R (Fin n → Rᵐᵒᵖ) := of_prod R _ _
      _ = (n + 1) • of R Rᵐᵒᵖ := by rw [ih, succ_nsmul']

/-- Every class is the class of a module in the ring-universe reference category. -/
theorem of_surjective :
    Function.Surjective (fun X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ ↦ of R X) := by
  intro a
  obtain ⟨X, rfl⟩ := TauCeti.objectCode_surjective a
  exact ⟨X, TauCeti.objectCode_congr (ModuleCat.FiniteProjective.reprIso Rᵐᵒᵖ X)⟩

/-- To prove a proposition about a class, it suffices to prove it on classes
of modules in the ring-universe reference category. -/
@[elab_as_elim]
theorem induction_on {p : ProjectiveClass R → Prop} (a : ProjectiveClass R)
    (h : ∀ X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ, p (of R X)) : p a := by
  obtain ⟨X, rfl⟩ := of_surjective R a
  exact h X

/-- Additive maps out of the class monoid are determined by their values on
finite projective module classes. -/
@[ext]
theorem addHom_ext {A : Type w} [AddZero A] {f g : ProjectiveClass R →+ A}
    (h : ∀ X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ, f (of R X) = g (of R X)) :
    f = g := by
  apply AddMonoidHom.ext
  intro a
  exact induction_on R a h

section LiftFunction

variable {A : Type w}
  (f : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ → A)
  (hiso : ∀ {X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ}, (X ≅ Y) → f X = f Y)

/-- Descend an isomorphism-invariant function on finite projective right modules
to a function on their isomorphism classes, with no algebraic structure on the target. -/
@[no_expose]
noncomputable def liftFunction
    (_hiso : ∀ {X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ}, (X ≅ Y) → f X = f Y) :
    ProjectiveClass R → A :=
  fun a ↦ f (Function.surjInv TauCeti.objectCode_surjective a)

/-- The descended function evaluates on a reference-module class as the supplied function. -/
@[simp]
theorem liftFunction_of (X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ) :
    liftFunction R f hiso (of R X) = f X := by
  apply hiso
  exact (TauCeti.objectCode_eq_objectCode_iff.1
    ((Function.surjInv_eq TauCeti.objectCode_surjective _).trans
      (TauCeti.objectCode_congr (ModuleCat.FiniteProjective.reprIso Rᵐᵒᵖ X)))).some

/-- For an input in any carrier universe, the descended function evaluates the
supplied function on its ring-universe representative. -/
theorem liftFunction_of_module :
    liftFunction R f hiso (of R M) =
      f (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M) := by
  rw [← of_repr R M]
  exact liftFunction_of R f hiso (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M)

/-- A descended function is uniquely determined by its values on reference-module classes. -/
theorem liftFunction_unique (F : ProjectiveClass R → A)
    (h : ∀ X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ, F (of R X) = f X) :
    F = liftFunction R f hiso := by
  funext a
  exact induction_on R a (fun X ↦ (h X).trans (liftFunction_of R f hiso X).symm)

end LiftFunction

section Lift

variable {A : Type w} [AddZero A]
  (f : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ → A)
  (hiso : ∀ {X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ}, (X ≅ Y) → f X = f Y)
  (hzero : f (ModuleCat.FiniteProjective.of Rᵐᵒᵖ PUnit.{u + 1}) = 0)
  (hadd : ∀ X Y : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ,
    f (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y)) = f X + f Y)

/-- Descend an isomorphism-invariant function on finite projective right modules
which preserves zero and direct sum to an additive map on their class monoid. -/
@[no_expose]
noncomputable def lift : ProjectiveClass R →+ A where
  toFun := liftFunction R f hiso
  map_zero' := by
    simpa only [of_zero] using
      (liftFunction_of R f hiso
        (ModuleCat.FiniteProjective.of Rᵐᵒᵖ PUnit.{u + 1})).trans hzero
  map_add' a b := by
    obtain ⟨X, rfl⟩ := of_surjective R a
    obtain ⟨Y, rfl⟩ := of_surjective R b
    rw [← of_prod R X Y]
    calc
      liftFunction R f hiso (of R (X × Y)) =
          f (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y)) :=
        liftFunction_of R f hiso (ModuleCat.FiniteProjective.of Rᵐᵒᵖ (X × Y))
      _ = f X + f Y := hadd X Y
      _ = liftFunction R f hiso (of R X) + liftFunction R f hiso (of R Y) := by
        rw [liftFunction_of, liftFunction_of]

/-- Forgetting the additive structure of the descended map gives the function descent. -/
theorem coe_lift :
    (lift R f hiso hzero hadd : ProjectiveClass R → A) = liftFunction R f hiso := by
  rfl

/-- The descended map evaluates on a reference-module class as the supplied function. -/
@[simp]
theorem lift_of (X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ) :
    lift R f hiso hzero hadd (of R X) = f X :=
  liftFunction_of R f hiso X

/-- For an input in any carrier universe, the descended map evaluates the
supplied function on its ring-universe representative. -/
theorem lift_of_module :
    lift R f hiso hzero hadd (of R M) =
      f (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M) := by
  exact liftFunction_of_module R M f hiso

/-- A descended additive map is uniquely determined by its values on module classes. -/
theorem lift_unique (F : ProjectiveClass R →+ A)
    (h : ∀ X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ, F (of R X) = f X) :
    F = lift R f hiso hzero hadd := by
  apply AddMonoidHom.ext
  intro a
  exact congrFun (liftFunction_unique R f hiso F h) a

end Lift

end ProjectiveClass

/-- The additive Grothendieck group of the direct-sum isomorphism-class monoid
of finite projective right `R`-modules. -/
abbrev K0 : Type u := Algebra.GrothendieckAddGroup (ProjectiveClass R)

namespace K0

/-- The canonical comparison with Tau Ceti's split Grothendieck group of finite
projective right modules. -/
noncomputable def splitK0Equiv :
    K0 R ≃+ TauCeti.SplitK0.{u} (TauCeti.finiteProjectiveModules Rᵐᵒᵖ).FullSubcategory :=
  (TauCeti.SplitK0.grothendieckAddGroupEquiv.{u} _).trans
    (TauCeti.SplitK0.mapEquiv.{u, u} (ModuleCat.FiniteProjective.tauCetiEquivalence Rᵐᵒᵖ))

/-- The canonical additive map from direct-sum isomorphism classes to K₀.
It is not asserted to be injective. -/
noncomputable abbrev ofClass : ProjectiveClass R →+ K0 R :=
  Algebra.GrothendieckAddGroup.of

variable (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]

/-- The K₀ generator associated to a finite projective right module in any
carrier universe. -/
noncomputable def of : K0 R := ofClass R (ProjectiveClass.of R M)

/-- The comparison sends a module generator to the split class of its
ring-universe representative, retaining the original right scalar action. -/
theorem splitK0Equiv_of :
    splitK0Equiv R (of R M) =
      TauCeti.SplitK0.of.{u} ((ModuleCat.FiniteProjective.tauCetiEquivalence Rᵐᵒᵖ).functor.obj
        (ModuleCat.FiniteProjective.repr Rᵐᵒᵖ M)) := by
  change TauCeti.SplitK0.mapEquiv.{u, u} _
    (TauCeti.SplitK0.grothendieckAddGroupEquiv.{u} _
      (Algebra.GrothendieckAddGroup.of (TauCeti.objectCode _))) = _
  rw [TauCeti.SplitK0.grothendieckAddGroupEquiv_of_objectCode,
    TauCeti.SplitK0.mapEquiv_of]

/-- The canonical completion map sends a module's isomorphism class to its K₀ generator. -/
theorem ofClass_of : ofClass R (ProjectiveClass.of R M) = of R M := rfl

/-- Right-linear equivalence preserves the K₀ generator. The converse is not
asserted: equality after group completion is weaker than module isomorphism. -/
theorem of_eq_of_equiv {N : Type w} [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] (e : M ≃ₗ[Rᵐᵒᵖ] N) :
    of R M = of R N :=
  congrArg (ofClass R) (ProjectiveClass.of_eq_of_equiv R M e)

/-- A carrier lift does not change the K₀ generator. -/
@[simp]
theorem of_ulift : of R (ULift.{w} M) = of R M := by
  simp only [of, ProjectiveClass.of_ulift]

/-- Every zero module gives the zero K₀ generator, without a nontrivial-ring premise. -/
@[simp]
theorem of_zero (Z : Type v) [AddCommGroup Z] [Module Rᵐᵒᵖ Z] [Subsingleton Z] :
    of R Z = 0 := by
  simp only [of, ProjectiveClass.of_zero, map_zero]

/-- Direct sum gives addition of K₀ generators. -/
@[simp]
theorem of_prod (N : Type w) [AddCommGroup N] [Module Rᵐᵒᵖ N]
    [Module.Finite Rᵐᵒᵖ N] [Module.Projective Rᵐᵒᵖ N] :
    of R (M × N) = of R M + of R N := by
  simp only [of, ProjectiveClass.of_prod, map_add]

/-- The group-completion universal property: additive maps from the class
monoid to any additive commutative group extend uniquely to K₀. -/
noncomputable def lift {G : Type w} [AddCommGroup G] :
    (ProjectiveClass R →+ G) ≃ (K0 R →+ G) :=
  Algebra.GrothendieckAddGroup.lift

/-- Restricting a K₀ homomorphism along the class map is the inverse universal map. -/
@[simp]
theorem lift_symm_apply {G : Type w} [AddCommGroup G] (f : K0 R →+ G) :
    (lift R).symm f = f.comp (ofClass R) := rfl

/-- The universal extension agrees with the given map on class generators. -/
theorem lift_ofClass {G : Type w} [AddCommGroup G]
    (f : ProjectiveClass R →+ G) (a : ProjectiveClass R) :
    lift R f (ofClass R a) = f a :=
  congrArg (fun h : ProjectiveClass R →+ G ↦ h a) ((lift R).symm_apply_apply f)

/-- Evaluation of the universal extension on a module generator. -/
@[simp]
theorem lift_of {G : Type w} [AddCommGroup G] (f : ProjectiveClass R →+ G) :
    lift R f (of R M) = f (ProjectiveClass.of R M) :=
  lift_ofClass R f (ProjectiveClass.of R M)

/-- K₀ homomorphisms are determined by their values on the class monoid. -/
theorem hom_ext_ofClass {G : Type w} [AddCommGroup G] {f g : K0 R →+ G}
    (h : ∀ a : ProjectiveClass R, f (ofClass R a) = g (ofClass R a)) : f = g := by
  apply (lift R).symm.injective
  exact AddMonoidHom.ext h

/-- K₀ homomorphisms are determined by values on finite projective module generators. -/
@[ext]
theorem hom_ext {G : Type w} [AddCommGroup G] {f g : K0 R →+ G}
    (h : ∀ X : ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ, f (of R X) = g (of R X)) :
    f = g := by
  apply hom_ext_ofClass R
  intro a
  obtain ⟨X, rfl⟩ := ProjectiveClass.of_surjective R a
  exact h X

end K0

end KTheory
