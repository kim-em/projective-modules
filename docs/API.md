# Current API guide

Import `ProjectiveModules` for the production aggregate. Focused imports below
reduce the dependency footprint. This is an authored guide to the migrated API,
not native doc-gen output or an exhaustive declaration catalogue. The
[overview](Overview.md) describes mathematical hypotheses and examples; the
[current sources](../ProjectiveModules/) give exact types and universes.

## Canonical constructions and imports

The package resolves Lean 4.36.0-rc1, Mathlib
`2cabef97b63d3275776b8b060d802de6a6fa1055` and Tau Ceti
`906780592fedf73008c25d5b4c16ae2321fc836d`.

| Interface | Import and characteristic use |
| --- | --- |
| Balanced tensor over a noncommutative ring | `TauCeti.LinearAlgebra.TensorProduct.Balanced.Actions`: `TauCeti.BalancedTensorProduct ℤ R M N`, `tmul ℤ R m n`, `balance ℤ R r m n`; the base `ℤ` imposes no commutativity on `R`. |
| Additive tensor universal property | [`ProjectiveModules.Module.BalancedTensorAdditive`](../ProjectiveModules/Module/BalancedTensorAdditive.lean): `TauCeti.BalancedTensorProduct.BalancedAddMap`, `liftAddHom`, `liftAddHom_tmul`, `addHom_ext`; `BalancedTensorExact` adds functorial maps and projective exactness on that carrier. |
| Right extension along `f : R →+* S` | [`ProjectiveModules.Module.RightExtension`](../ProjectiveModules/Module/RightExtension.lean): `ModuleCat.RightExtension.Obj f M`, `tmul f m s`, `map`, `adjunction`; the right action is Tau Ceti's outer action on coefficients. Rings may be noncommutative and carrier universes are independent. |
| Scalar restriction of projectivity | `TauCeti.Algebra.Module.Projective.Trans`: `Module.Projective.trans`. |
| Arbitrary-rank PID freeness | `TauCeti.LinearAlgebra.FreeModule.PID`: `Submodule.free_of_isPrincipalIdealRing`; apply `Module.Free.of_injective_of_projective_of_isPrincipalIdealRing` to the identity for projective-module freeness. |
| Self-injective coefficients | `TauCeti.Algebra.Module.Injective.SelfInjective`: `Module.Injective.of_finite_projective`, with regular-module injectivity supplied explicitly. |
| Ordinary-coefficient bidual | `TauCeti.LinearAlgebra.Dual.Opposite`: `TauCeti.opDualEvalEquiv R M`, its evaluation and naturality formulas, and `opDualCodomainEquiv` for opposite coefficients. [`Module.Bidual`](../ProjectiveModules/Module/Bidual.lean) retains comparisons with commutative evaluation. |
| Full exterior-algebra base change | `Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange`: `(ExteriorAlgebra.baseChangeEquiv R M S).symm` has the former exterior-algebra-first orientation. |
| Fixed-degree exterior base change | `TauCeti.LinearAlgebra.ExteriorPower.BaseChange`: `TauCeti.exteriorPower.equivBaseChange`; no flatness hypothesis is needed for the carrier equivalence. |
| Top exterior coordinates | `TauCeti.LinearAlgebra.ExteriorPower.Basis`: `Module.Basis.exteriorPowerTopEquiv`, its generator and inverse formulas. [`ExteriorPower.Top`](../ProjectiveModules/ExteriorPower/Top.lean) adds invertibility and the custom-determinant comparison. |
| Product exterior pairing | `TauCeti.LinearAlgebra.ExteriorPower.Prod`: `TauCeti.exteriorPower.wedgeTensor`; [`ExteriorPower.ProdPairing`](../ProjectiveModules/ExteriorPower/ProdPairing.lean) and [`DirectSum`](../ProjectiveModules/ExteriorPower/DirectSum.lean) retain bijectivity and the whole Sum Formula. |
| Compact elements and module equivalences | `TauCeti.Order.CompactlyGenerated` and `TauCeti.Algebra.Category.ModuleCat.Equivalence`: `OrderIso.isCompactElement_iff (a := k)`, `e.submoduleOrderIso X`, `e.finite_functor_obj_iff X`. |
| Semisimple presentation | `TauCeti.RingTheory.Semisimple.Wedderburn.Presentation`: `TauCeti.WedderburnPresentation`, `TauCeti.IsSemisimpleRing.wedderburnPresentation`; fields `blockCount`, `divisionRing`, `degree`, `equiv`. |
| Stable quotient | `TauCeti.CategoryTheory.Exact.Stable.Basic` for `E := TauCeti.ExactStructure.abelian (ModuleCat R)`: `E.ProjectiveStableCategory`, `E.projectiveStableFunctor`, its map-zero criterion and summand API. [`Category.Stable`](../ProjectiveModules/Category/Stable.lean) retains Ext¹ detection. |
| Finite projective classes and K₀ | [`KTheory.K0`](../ProjectiveModules/KTheory/K0.lean): `KTheory.ProjectiveClass R` uses Tau Ceti `ObjectCode` over finite projective right modules; `ProjectiveClass.of` and `K0.of` accept arbitrary carrier universes. `ModuleCat.FiniteProjective.tauCetiEquivalence` identifies ring-universe objects with `(TauCeti.finiteProjectiveModules R).FullSubcategory`; `K0.splitK0Equiv` compares the completion with `TauCeti.SplitK0` of that canonical category over `Rᵐᵒᵖ`. |
| Tensor-product K₀ ring | [`KTheory.Ring`](../ProjectiveModules/KTheory/Ring.lean) uses `TauCeti.RingTheory.GrothendieckRing`; Group Theory's duplicate ring implementation is no longer imported. |

Tau Ceti source links are rooted at the
[pinned Tau Ceti tree](https://github.com/TauCetiProject/TauCeti/tree/906780592fedf73008c25d5b4c16ae2321fc836d/TauCeti),
and Mathlib links at the
[pinned Mathlib tree](https://github.com/leanprover-community/mathlib4/tree/2cabef97b63d3275776b8b060d802de6a6fa1055/Mathlib).

## Specialized mathematics retained here

| Family | Entry points |
| --- | --- |
| Right-extension comparisons | [`RightExtensionComparison`](../ProjectiveModules/Module/RightExtensionComparison.lean), [`ComparisonCoherence`](../ProjectiveModules/Module/RightExtensionComparisonCoherence.lean), [`TensorProduct`](../ProjectiveModules/Module/RightExtensionTensorProduct.lean), [`Quotient`](../ProjectiveModules/Module/RightExtensionQuotient.lean), [`Ideal`](../ProjectiveModules/Module/RightExtensionIdeal.lean), [`Free`](../ProjectiveModules/Module/RightExtensionFree.lean). |
| Projective trace and contractions | [`Trace.Basic`](../ProjectiveModules/Module/Trace/Basic.lean), [`Trace.Partial`](../ProjectiveModules/Module/Trace/Partial.lean), [`Dual.BaseChange`](../ProjectiveModules/Dual/BaseChange.lean), [`Contraction.BaseChange`](../ProjectiveModules/Contraction/BaseChange.lean); finite-projective semimodule hypotheses remain broader than finite-free trace APIs. |
| Splittings and complements | [`ProjectiveKernel`](../ProjectiveModules/Module/ProjectiveKernel.lean), [`ProjectiveComplement`](../ProjectiveModules/Module/ProjectiveComplement.lean), [`CommutingProjections`](../ProjectiveModules/Module/CommutingProjections.lean). |
| Determinants and rank | [`DeterminantLine`](../ProjectiveModules/ExteriorPower/DeterminantLine.lean), [`StalkRank`](../ProjectiveModules/ExteriorPower/StalkRank.lean), [`RankFiberDecomposition`](../ProjectiveModules/Module/RankFiberDecomposition.lean), [`ComponentwiseFree`](../ProjectiveModules/Module/ComponentwiseFree.lean). |
| Stable and free modules | [`StablePresentation`](../ProjectiveModules/Free/StablePresentation.lean), [`LocalRing`](../ProjectiveModules/Module/LocalRing.lean), [`InfiniteCoordinates`](../ProjectiveModules/Free/InfiniteCoordinates.lean), [Noetherian guide](NoetherianSubmodule.md). |
| Specialized K₀ | [`KTheory`](../ProjectiveModules/KTheory/): scalar extension, Morita equivalence, products, dimensions, determinant, trace, duality, nilpotent invariance and semisimple coordinates. |

The [historical API display and manifest](history/README.md) document an earlier
source snapshot. Their native provenance has not been relabelled as current.
