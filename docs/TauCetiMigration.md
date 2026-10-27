# Tau Ceti dependency migration

The library uses Tau Ceti `906780592fedf73008c25d5b4c16ae2321fc836d`,
Mathlib `2cabef97b63d3275776b8b060d802de6a6fa1055` and Lean 4.36.0-rc1.

Balanced tensors use `TauCeti.BalancedTensorProduct ℤ R M N` and its right
coefficient action. Stable quotients use the projective stable category of the
abelian exact structure. Finite-projective classes use Tau Ceti object codes;
`K0.splitK0Equiv` identifies their Mathlib group completion with Tau Ceti's
split K₀ of the canonical finite-projective category over `Rᵐᵒᵖ`.
The independent-universe category and representative API remain available.

The migration also replaces duplicated scalar-restriction, PID, injectivity,
Wedderburn, compactness, dual, bidual and exterior constructions, and uses
Tau Ceti's orthogonal-idempotent decomposition. Additional projective trace,
right-extension, exactness, determinant, rank and coherence results remain
in this library. The [current API guide](API.md) lists their providers.

Production source changes from 143 files and 32,958 lines to 135 files
and 31,260 lines: **1,698 fewer lines (5.2%)**,
including comments and blanks. Nine obsolete modules are removed, one
additive tensor interface is added, 42 retained production files are edited,
and 32 of the 118 test files are updated. Counts exclude dependencies,
the aggregate root and documentation.

Validation completed locally:

- `lake update` resolves the committed Git dependency graph.
- `lake build` passes both default library and test targets (7,364 jobs).
- All 11 Python documentation-adapter tests pass.
- `git diff --check` and current documentation-link checks pass.

The build emits existing-style deprecation and private-module warnings.
No heartbeat limits or lint settings were relaxed. The historical native API
records are preserved under [history](history/README.md); the current guide
is authored documentation and makes no new native-generation claim.
