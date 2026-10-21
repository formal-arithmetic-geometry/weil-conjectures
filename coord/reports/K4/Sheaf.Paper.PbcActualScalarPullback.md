## What changed

Filled the two proofs in `Sheaf.Paper.PbcActualScalarPullback`, preserving every existing
signature and definition. The right-adjoint comparison is Mathlib's
`SheafOfModules.pushforwardCongr` for the supplied coefficient square, with uniqueness
by sectionwise extensionality. The derived comparison descends the ordinary complex
comparison conjugated by the two composite cochain counits on flat-term K-flat
representatives. The proof establishes invertibility of those counits using the
existing K-flat preservation and computation theorems, and proves the prescribed
normalization and uniqueness by cancellation and faithful restriction.

Added proved private helpers for the ring-sheaf comparison, K-flat preservation,
cochain counits and their invertibility, and resolving descent. The generic
ring-sheaf comparison and generic resolving-descent helper keep the large concrete
coefficient functors out of those categorical constructions during kernel checking. Proof imports supply pro-etale algebraic inverse image, independent
coefficient change-of-rings preservation, set inverse-image finite-limit preservation,
and resolving localization. The latter is
imported with `all` to reuse its proved one-variable localization and precomposition
helpers. Updated the owning definition node's proof, proof dependencies and origin.

## Proved and sorry left

Closed the two original holes:

- `AlgebraicGeometry.Scheme.pbcActualScalarRightIso_exists`.
- `AlgebraicGeometry.Scheme.pbcActualScalarDerivedPullIso_exists`.

No holes added or split off. No `sorry` remains in the item. Existing imported
statements remain their own items; this delivery does not claim to close their holes.

## No longer needed

Removed these unused or redundant proof imports:

- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`.
- `Sheaf.Paper.RingedTopoiDerivedPullback`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`.
- `Mathlib.Algebra.Homology.BifunctorShift`.
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`.

No module or node is withdrawn. The proof needs no separate tensor-descent,
ringed-derived-pullback, telescope-closure or tensor-adjunction construction.
The existing public imports are retained because they are part of the module's public
interface. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The actual scalar-comparison declarations are owned by
`def-weil-pbc-normalized-scalar-restriction`; their docstrings still cite the broader
tensor-pullback node. The owning definition node previously had no proof steps or
proof dependencies. This packet records the actual proof there without changing the
statement or its Lean attachment. The scalar comparison uses arbitrary compatible
coefficient morphisms and makes no invertibility assumption on the structure maps.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
