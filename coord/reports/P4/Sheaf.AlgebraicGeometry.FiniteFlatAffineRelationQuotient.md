## What changed

Proved `AlgebraicGeometry.finiteFlat_affineRelation_quotient` by composing the four
intermediate results already named in its current DAG node:
`affineRelation_comparison_preparation`, `affineGroupoid_local_basis_reduction`,
`affineRelation_flat_local_descent`, and `fppf_kernelPair_quotient_descent`.
The theorem statement and both invariant-ring constructions are unchanged.

Added two proved private helpers. `tensorComparison_of_basis` identifies the two
base-change tensor presentations and transfers finite freeness by tensor symmetry.
`smallSheafification` transports the canonical unit and its universal property from
universe-lifted presheaves to ordinary presheaves using the fully faithful ULift functor
and preservation of coequalizers. The main proof also derives endpoint injectivity
from the given monomorphism and supplies all coordinate-ring and scalar-tower glue.
Updated the item node's proof to record these arguments.

Validation: `lcompile.py` compiled the full item cleanly in 14.6 seconds.
A textual comparison checked that the public theorem signature and both public
definition bodies are unchanged. The DAG proof-dependency union was checked,
and the delivered Lean has zero `sorry` tokens and no lines over 100 characters.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.finiteFlat_affineRelation_quotient`
(node `lem-a1-finite-flat-affine-relation-quotient`). Zero holes added; zero holes
remain in the delivered module. Both private helpers are proved. The four imported
intermediate theorems retain their existing proofs/holes and are not changed by this
delivery. This is a proof from existing stated dependencies, not a new decomposition.

## No longer needed

Replaced the following old private proof imports with the four current intermediate
modules and Mathlib's ULift/coequalizer preservation modules:

- `Mathlib.CategoryTheory.Yoneda`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.RingTheory.Flat.Basic`
- `WeilConjectures.RingTheory.FlatLocalExtensionGivenResidueField`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
- `Mathlib.RingTheory.Flat.Localization`
- `WeilConjectures.AlgebraicGeometry.FinitePushforwardLocallyFree`
- `Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum`
- `Mathlib.RingTheory.Ideal.GoingUp`
- `WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant`
- `WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`
- `Mathlib.Algebra.Module.LocalizedModule.Exact`
- `Sheaf.RingTheory.FinitePresentationAndFlatOfFiniteFreeStandardCover`
- `WeilConjectures.Mathlib.RingTheory.Finiteness.Descent`
- `Mathlib.RingTheory.Flat.EquationalCriterion`
- `WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.CategoryTheory.Sites.LocallyBijective`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
- `Mathlib.CategoryTheory.Sites.Precoverage`
- `Sheaf.AlgebraicGeometry.AffineGroupoidBasisDescent`
- `Sheaf.AlgebraicGeometry.AffineGroupoidIntegralInvariants`
- `Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres`
- `Sheaf.RingTheory.SemilocalSubmoduleBasis`

These are removals from this module's direct proof imports. Their mathematical inputs
remain used through the four intermediate nodes, so no global withdrawal or claim
that these nodes are unreachable is made. No public import was removed, and no node
or module is withdrawn. The current DAG already lists exactly the four dependencies
used in this proof; none of those four can be pruned.

Removed the obsolete direct `tool_uses` approvals from the earlier thirteen-step node:

- `lem-weil-pbc-flat-local-extension-given-residue-field`
- `lem-sc-finite-pushforward-locally-free`
- `lem-weil-pbc-finite-free-algebra-spectrum`
- `lem-weil-pbc-finite-locally-free-degree-locally-constant`
- `lem-weil-pbc-fibre-degree-base-change`
- `lem-sc-affine-standard-cover-finite-presentation-flat`
- `lem-trf-finite-presentation-module-descent-flat-local`
- `lem-weil-pbc-finite-projective-standard-free-cover`
- `lem-galois-yoneda-fully-faithful`
- `lem-weil-pbc-flat-lfp-open`
- `lem-trf-fppf-covering-base-change`

These nodes remain mathematical inputs of the four intermediate results.

## Where the brief, the DAG or earlier work was wrong

The module docstring still describes the original thirteen-step proof, whereas the
current DAG has already factored those steps into four intermediate results. The
published signatures also use different tensor orders and quotient-descent universes.
The delivery proves the needed identifications rather than restating dependencies or
changing the item statement. The zero-ring case is handled uniformly: for each prime
of C, C and A are nontrivial, and if there are no primes the local hypotheses are vacuous.

The unit's statement and route are unchanged. No other existing module is modified.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
