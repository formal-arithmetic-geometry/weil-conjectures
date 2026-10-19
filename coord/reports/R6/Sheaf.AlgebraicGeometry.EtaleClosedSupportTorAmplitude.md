## What changed

Proved AlgebraicGeometry.Etale.closedImmersion_rightAdjoint_torAmplitude with its
original signature and exceptional inverse-image definition unchanged. The proof first
uses closedImmersion_rightAdjoint_amplitude to establish bounded constructibility,
then applies a finite-constant tensor bound and the published residue Tor criterion.

Added Sheaf.AlgebraicGeometry.EtaleClosedSupportResidueBound and its proved theorem
AlgebraicGeometry.Etale.closedSupport_finiteTensor_vanishing. Its proof tensors the
support triangle, uses the open projection formula and its unit identity, completes a
morphism of distinguished triangles, and applies monoidal closed pullback and the
fully faithful closed direct-image counit. All private helpers are proved.

Only these two Lean modules and their two node records are delivered. The coefficient
ring and residue-test sources are unchanged. Both delivery modules passed lcompile.py
as a set: 1.5 seconds for the tensor bound and 15.3 seconds for the item.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Etale.closedImmersion_rightAdjoint_torAmplitude
(prop-exc-closed-tor). Added zero holes. The new theorem
AlgebraicGeometry.Etale.closedSupport_finiteTensor_vanishing
(lem-exc-closed-residue-bound) and all private helpers have complete proofs.
Both delivered modules contain zero sorry. This is a proof, not a decomposition.

## No longer needed

The following declared proof dependencies are unused by the new route:
lem-constructible-constant-exact, lem-kun-kflat-criteria,
lemma-weil-pbc-finite-direct-image-exact, lemma-weil-pbc-finite-stalk-formula,
prop-weil-pbc-geometric-stalks-exact, and lemma-weil-pbc-geometric-stalk-conservative.
The monoidal closed pullback and its counit replace the explicit closed tensor
resolution and stalk calculation. Their obsolete top-level tool_uses entries are removed.

Removed proof imports for those dependencies:
WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact,
Sheaf.Paper.EtaleKFlatCriteria, WeilConjectures.SixFunctors.Finite.Exact,
WeilConjectures.SixFunctors.Finite.Stalk,
WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint,
Mathlib.CategoryTheory.Sites.Point.Basic, Mathlib.CategoryTheory.Sites.Point.Skyscraper,
and Mathlib.Algebra.Homology.ShortComplex.ShortExact.

The main module also removes the following direct proof imports, whose necessary
functionality is used through the finite-tensor bound module:
Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectImageCoproducts,
WeilConjectures.SixFunctors.Etale.Derived.Tensor,
WeilConjectures.SixFunctors.Etale.Derived.Triangulated,
WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection,
Mathlib.CategoryTheory.Triangulated.Pretriangulated,
Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle, and
Sheaf.AlgebraicGeometry.ExceptionalConstantTensor.
Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex is not separately
required: the coproduct theorem encapsulates that argument. Removed a duplicate public
import of WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf and a
duplicate proof import of ConstantEtaleSheafShortExact.
These are route-specific pruning claims; other targets may still use the modules.

## Where the brief, the DAG or earlier work was wrong

The original plan used a resolution and geometric stalks for the closed tensor
comparison. The shorter monoidal closed-pullback argument proves the same comparison.
The unit realization record is unchanged. Bounded constructibility already provides
an ordered cohomology interval, so no case split on the Tor interval is needed.

Earlier sandbox reports proposed changing the coefficient-ring representation and
recompiling its consumers. The final packet requires no such definition change.
It compiles against the published coefficient and residue-test interfaces.

## New nodes

lem-exc-closed-residue-bound records the proved finite-constant tensor bound, with
no constructibility hypothesis. It isolates the tensor-support paragraphs of
prop-exc-closed-tor and is strictly one part of the parent argument: the parent still
proves constructibility and applies the residue criterion. The statement applies to
any finite module N, specializing to the residue module in the parent. Edge cases
N=0, empty schemes, a>b, and c=0 are retained. Its source, proof steps, actual search
records, and Lean declaration are recorded in the node. No change record is needed
because no existing definition or signature is changed.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
