## What changed

Proved five existing theorems in `Sheaf.Paper.WeilTensorProduct` without changing
any statement or mathematical definition data. The first-variable derived-tensor computation uses
K-flat resolutions, the existing categorical K-flat acyclicity criterion and the
descent comparison. Pullback preserves
completeness by the completion comparison unit square. The constructible rational
inclusion uses scalar extension and denominator cancellation for uniqueness among
arbitrary functors. Its pullback object identity follows from integral normalization.
The rational tensor comparison uses reflector uniqueness, integral naturality and
tensor induction. Added private proved helpers and proof-only imports for these
arguments, and updated node `def-wf-tensor-product` to describe them. Reused the
existing independent-universe cochain tensor structures instead of constructing
custom cone and preadditivity helpers. Local irreducibility annotations keep intrinsic completion, scalar composition
and constructed functors from unfolding during later morphism calculations.
The existing tensor-functor-law proof now uses only explicit zero, pure-tensor
and composition equations, replacing broad simplification. These annotations do not change exported data
or downstream elaboration settings.

The complete optimized module compiled successfully through `lcompile.py` in 29.9 seconds
with no diagnostics. The Frobenius isomorphism now supplies its two inverse laws explicitly;
its hom and inv fields are unchanged. The requested change record is
`coord/changes/wfTensorFrobenius-explicit-laws.md`. The declaration-specific downstream
scan found no external consumers, so no adaptations are needed.
The earlier failed delivery checks pushed nothing. Delivery validation is rerun
against the completed packet.

## Proved and sorry left

Closed five of the original ten holes:

- `SheafOfModules.wfSiteDerivedTensor_first`.
- `AlgebraicGeometry.Scheme.wfIsoPullback_complete`.
- `AlgebraicGeometry.Scheme.wfRationalTensorPullback_exists`.
- `AlgebraicGeometry.Scheme.wfConstructibleInclusion_exists`.
- `AlgebraicGeometry.Scheme.wfConstructiblePullback_obj`.

Five original holes remain, all attached to node `def-wf-tensor-product`:

- `AlgebraicGeometry.Scheme.wfTensorRepresentative_exists`.
- `AlgebraicGeometry.Scheme.wfRationalTensorHom_exists`.
- `AlgebraicGeometry.Scheme.wfPullbackCompletion_exists`.
- `AlgebraicGeometry.Scheme.wfCompletePullback_linear`.
- `AlgebraicGeometry.Scheme.wfConstructible_complete`.

No holes were added or split off. All remaining holes are existing named theorems
with their source and proof plan in the module docstrings.

## No longer needed

No baseline import or target-reachable module was pruned. The custom cone route
was replaced by the existing categorical K-flat interface. It needs no direct
imports of `Mathlib.Algebra.Homology.BifunctorFlip`,
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`,
`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`, or
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`; those exploratory
proof imports were removed. The corresponding custom preadditivity and cone
helpers were removed. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier report described three unverified candidate proofs and seven holes.
The current packet has five verified proof closures and five holes. Earlier
compile-server transport failures and deterministic elaboration failures were
resolved before the successful full-module compilation; no failed check landed
or pushed any code. No statement dispute or change to mathematical definition data is introduced. The first
preflight requested a change record for the explicit Frobenius inverse-law fields; that
record is now included.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
