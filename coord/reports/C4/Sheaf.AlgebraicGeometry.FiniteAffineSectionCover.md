## What changed

Proved `AlgebraicGeometry.exists_finite_affine_section_cover` with its exact original signature.
The proof follows Stacks Project Tag 03HW using finite tensor products of `AdjoinRoot` algebras
as the monic presentation algebra. It constructs the actual pullback comparison through a
pushout of rings and affine comparison isomorphisms, then transports the closed immersion.

Added three fully proved support modules:

- `Sheaf.RingTheory.FiniteMonicSplitting`: successive finite free splitting extensions, including
  the zero-ring identity case, and faithfulness of the resulting extension.
- `Sheaf.RingTheory.MonicTensorPresentation`: the tensor presentation, its evaluation maps,
  its finite power-tensor basis, and surjectivity for a generating tuple.
- `Sheaf.RingTheory.SplitMonicTensorSections`: a finite family of evaluation quotients covers
  the prime spectrum. This uses a domain quotient at each prime, never a domain hypothesis
  on the base ring.

Existing public imports and existing declaration signatures are unchanged. Added proof imports
of the support modules and `Mathlib.AlgebraicGeometry.PullbackCarrier` for surjectivity under
base change. Updated the original docstring's proof and the node's proof dependencies to the
implemented route. No definition or statement repair, consumer adaptation, or change record
is required. The unit's fixed three-step proper-base-change route is preserved.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_finite_affine_section_cover`
(`lem-weil-pbc-finite-affine-section-cover`).

Added zero holes and split off zero unfinished obligations. Every declaration in the three
new modules is proved; there are zero `sorry` tokens in all four delivered Lean files.
In particular the new public results are:
`exists_faithful_finite_free_splitting`,
`MonicTensorPresentation.presentationMap_surjective`, and
`MonicTensorPresentation.exists_cover`.

The existing imported theorem
`AlgebraicGeometry.specMap_isFiniteLocallyFree_of_basis`
(`lem-weil-pbc-finite-free-algebra-spectrum`) remains an upstream proof dependency with its
pre-existing hole. This delivery neither adds nor duplicates that hole.

Edge cases checked in the actual argument: zero base ring (identity splitting extension),
zero target algebra, empty generators and empty equation family (empty tensor product),
constant monic equations (possibly zero presentation algebra and empty cover), nilpotents,
and repeated roots. The section-cover proof extracts factors only in the domain quotient by
a prime. No chosen witness from an unproved existence theorem is used to define data.

## No longer needed

Removed original proof imports:
`Mathlib.RingTheory.AdjoinRoot`,
`Mathlib.RingTheory.Spectrum.Prime.Topology`, and
`Mathlib.LinearAlgebra.TensorProduct.Basis`.
The first two APIs are supplied by the new support modules; the binary tensor basis API is
not used. Kept `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` for integrality.

The original dependency `lem-weil-pbc-free-module-base-change-free` is no longer needed on
this route: the final pullback projection is finite locally free and surjective directly by
Mathlib base-change instances. Removed it from the parent's proof dependencies.

The original one-polynomial splitting and monic-quotient dependencies are still used inside
the proved support results; they have moved into those nodes' proof dependencies and are
not claimed as globally pruned. The tensor-product affine-spectrum, closed-immersion,
integrality, lying-over, finite-free spectrum and free-module dependencies remain used.
No existing Sheaf module is withdrawn or claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original plan's separate empty-scheme branch,
positive-degree modification, multivariable/iterated-quotient comparison, and final explicit
base-changed-basis calculation are unnecessary. The tensor algebra is a real construction;
its power basis follows directly from Mathlib's `Basis.piTensorProduct`. Existing spectrum
and base-change APIs complete the scheme construction.

Searches were performed with LeanFinder, Loogle, LeanSearch and Mathlib/source grep. They
found the single-equation splitting lemma and the tensor basis API, but no assembled
simultaneous splitting, tensor evaluation surjectivity, or prime-spectrum section cover.
Blueprint searches for monic tensor, simultaneous splitting, closed sections, monic quotient
and adjoin roots found no duplicate of the three new assembled results.

## New nodes

`lem-weil-pbc-finite-monic-simultaneous-splitting` records
`exists_faithful_finite_free_splitting` in `Sheaf.RingTheory.FiniteMonicSplitting`.
It is proved by induction using the existing single-equation splitting lemma, transitivity
of finite free modules, and faithfulness of a free nonzero module.

`lem-weil-pbc-monic-tensor-presentation` records the real tensor algebra, its finite power
basis and its evaluation-surjectivity theorem in `Sheaf.RingTheory.MonicTensorPresentation`.
It is proved from the monic quotient basis, the finite tensor basis and range containment.

`lem-weil-pbc-split-monic-tensor-sections` records
`MonicTensorPresentation.exists_cover` in `Sheaf.RingTheory.SplitMonicTensorSections`.
It is proved by extracting vanishing linear factors modulo each prime and comparing the
resulting evaluation map with the quotient map on all tensor factors.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
