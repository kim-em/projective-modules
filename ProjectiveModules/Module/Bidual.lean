/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import TauCeti.LinearAlgebra.Dual.Opposite
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Ordinary-coefficient bidual evaluation

For a left module `M` over a semiring `R`, the first Hom `M →ₗ[R] R` carries
pointwise right multiplication, expressed as an `Rᵐᵒᵖ`-module structure.
Its ordinary-coefficient second Hom carries pointwise left multiplication by `R`.
Evaluation is Mathlib's mixed-scalar `LinearMap.flip` applied to the identity.
No right action on `M` is required, and the scalar and source universes are
independent.

`TauCeti.opDualEvalEquiv` bundles this evaluation for finite projective modules.
For commutative semirings, restriction of the second Hom's inner scalars compares
it with Mathlib's `Module.evalEquiv` without changing the coefficient carrier.

## References

The evaluation construction and its mixed-scalar linearities use Mathlib's
bilinear-map and opposite-module APIs. The commutative finite-projective case
is Mathlib's `Module.IsReflexive` and `Module.evalEquiv`.
For the finite-projective duality context, see Charles A. Weibel,
*The K-book*, Chapter I, §2.
-/

@[expose] public section

universe uR uM

namespace LinearMap

/-- Over a commutative semiring, restriction of the second Hom's inner scalars
turns mixed-scalar evaluation into the same-scalar dual evaluation. -/
theorem flip_id_restrictScalars_eq_dual_eval
    (R : Type uR) (M : Type uM)
    [CommSemiring R] [AddCommMonoid M] [Module R M] :
    (LinearMap.restrictScalarsₗ
      (R := R) (S := Rᵐᵒᵖ) (M := M →ₗ[R] R) (N := R) (R₁ := R)).comp
        (LinearMap.flip (LinearMap.id :
          (M →ₗ[R] R) →ₗ[Rᵐᵒᵖ] (M →ₗ[R] R))) = Module.Dual.eval R M := by
  apply LinearMap.ext₂
  intro m f
  simp only [LinearMap.comp_apply, LinearMap.restrictScalarsₗ_apply,
    LinearMap.restrictScalars_apply, LinearMap.flip_apply, LinearMap.id_apply,
    Module.Dual.eval_apply]

/-- The coefficient-preserving inner-scalar conversion agrees with the
commutative finite-projective evaluation equivalence. -/
theorem opDualEvalEquiv_restrictScalars
    (R : Type uR) (M : Type uM)
    [CommSemiring R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    (LinearMap.restrictScalarsₗ
      (R := R) (S := Rᵐᵒᵖ) (M := M →ₗ[R] R) (N := R) (R₁ := R)).comp
        (TauCeti.opDualEvalEquiv R M).toLinearMap =
      (Module.evalEquiv R M).toLinearMap := by
  apply LinearMap.ext₂
  intro m f
  change TauCeti.opDualEvalEquiv R M m f = Module.evalEquiv R M m f
  rw [TauCeti.opDualEvalEquiv_apply, Module.evalEquiv_apply, Module.Dual.eval_apply]

/-- The two inner-scalar restrictions on the ordinary-coefficient second Hom
are inverse conversions over a commutative semiring. -/
theorem bidual_restrictScalars_roundTrips
    (R : Type uR) (M : Type uM)
    [CommSemiring R] [AddCommMonoid M] [Module R M] :
    (LinearMap.restrictScalarsₗ
      (R := Rᵐᵒᵖ) (S := R) (M := M →ₗ[R] R) (N := R) (R₁ := R)).comp
        (LinearMap.restrictScalarsₗ
          (R := R) (S := Rᵐᵒᵖ) (M := M →ₗ[R] R) (N := R) (R₁ := R)) = LinearMap.id ∧
      (LinearMap.restrictScalarsₗ
        (R := R) (S := Rᵐᵒᵖ) (M := M →ₗ[R] R) (N := R) (R₁ := R)).comp
        (LinearMap.restrictScalarsₗ
          (R := Rᵐᵒᵖ) (S := R) (M := M →ₗ[R] R) (N := R) (R₁ := R)) = LinearMap.id := by
  constructor
  · apply LinearMap.ext₂
    intro Φ f
    rfl
  · apply LinearMap.ext₂
    intro Ψ f
    rfl

end LinearMap
