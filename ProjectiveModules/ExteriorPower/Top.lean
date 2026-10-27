/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Prism
module

public import TauCeti.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.StdBasis
public import ProjectiveModules.ExteriorPower.Determinant

/-!
# Top exterior powers and ordinary determinants

A basis indexed by `Fin n` canonically identifies the `n`th exterior power
with the base ring: the coordinate of an exterior product is its determinant
in that basis. Under this identification, the exterior-power action of an
endomorphism is multiplication by `LinearMap.det`.

For the standard basis of `Fin n → R`, this identifies the conditional
`exteriorPower.determinant` with `LinearMap.det` and, for `Matrix.toLin'`, with
`Matrix.det`. All results include degree zero and the zero ring.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module.Basis

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {n : ℕ} (b : Basis (Fin n) R M)

/-- The top exterior coordinate intertwines an endomorphism with its determinant. -/
theorem exteriorPowerTopEquiv_map (f : Module.End R M) (x : ⋀[R]^n M) :
    b.exteriorPowerTopEquiv (exteriorPower.map n f x) =
      LinearMap.det f * b.exteriorPowerTopEquiv x := by
  obtain ⟨y, rfl⟩ := b.exteriorPowerTopEquiv.symm.surjective x
  rw [Module.Basis.exteriorPowerTopEquiv_symm_apply, map_smul, map_smul]
  simp only [exteriorPower.map_apply_ιMulti, Module.Basis.exteriorPowerTopEquiv_apply_ιMulti,
    Module.Basis.det_comp, Module.Basis.det_self, mul_one, smul_eq_mul, map_smul]
  exact mul_comm _ _

/-- A basis indexed by `Fin n` proves that the top exterior power is invertible. -/
theorem topExteriorInvertible (b : Basis (Fin n) R M) :
    Module.Invertible R (⋀[R]^n M) :=
  Module.Invertible.congr (b.exteriorPowerTopEquiv).symm

/-- The determinant defined through an invertible top exterior power agrees
with the ordinary finite-free determinant. -/
theorem exteriorPower_determinant_eq_det (b : Basis (Fin n) R M)
    [Module.Invertible R (⋀[R]^n M)] (f : Module.End R M) :
    exteriorPower.determinant R M n f = LinearMap.det f := by
  rw [exteriorPower.determinant_eq_iff_map_eq_smul]
  intro x
  apply (b.exteriorPowerTopEquiv).injective
  rw [b.exteriorPowerTopEquiv_map, map_smul]
  rfl

end Module.Basis

namespace exteriorPower

variable (R : Type u) [CommRing R]

/-- The standard top exterior power of `R^n` is invertible. -/
instance instInvertiblePiTop (n : ℕ) :
    Module.Invertible R (⋀[R]^n (Fin n → R)) :=
  (Pi.basisFun R (Fin n)).topExteriorInvertible

/-- On the standard free module, the exterior-power determinant is
`LinearMap.det`. -/
theorem determinant_pi_eq_det (n : ℕ) (f : Module.End R (Fin n → R)) :
    determinant R (Fin n → R) n f = LinearMap.det f :=
  (Pi.basisFun R (Fin n)).exteriorPower_determinant_eq_det f

/-- On a matrix endomorphism, the exterior-power determinant is `Matrix.det`. -/
theorem determinant_toLin' (n : ℕ) (g : Matrix (Fin n) (Fin n) R) :
    determinant R (Fin n → R) n (Matrix.toLin' g) = Matrix.det g := by
  rw [determinant_pi_eq_det, LinearMap.det_toLin']

end exteriorPower
