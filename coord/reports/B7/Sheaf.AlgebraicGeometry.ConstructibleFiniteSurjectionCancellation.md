## What changed

Proved `AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_finite_surjective`
with its exact original signature. All original public imports remain. The proof converts
between finite constant-value and finite-stalk constructibility, and between bounded-below
and unbounded derived direct images. Negative degrees vanish by left t-exactness.

For every constructible Q, use the surjective adjunction unit to embed Q into pi_*pi^*Q.
Constructible pullback and the existing assigned finite-direct-image theorem make the latter
constructible. An explicit three-factor isomorphism, using exactness of finite direct image,
identifies its derived f-image with the derived composite image of pi^*Q. The hypothesis
makes this good. The already proved source-library finite-order resolution principle then
proves constructibility for every sheaf. Convert its conclusion back to the original
predicate. No uniform vanishing assertion is introduced.

Added proof-only imports of
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage`,
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective`,
`WeilConjectures.SixFunctors.Finite.Exact`, and
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`.
The finite constructible direct-image import is retained. Updated the item's DAG route and
recorded the existing resolution principle in a new node, without a new Lean declaration.
No definition, signature, visibility, universe or target changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.hasConstructibleHigherDirectImages_of_finite_surjective`
(node `lem-finrepair-finite-surjection-cancellation`).
Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0. Split-offs: 0.
This is a proof from existing declarations, not a decomposition.

The final proof compiles through lcompile.py without errors or warnings.
`#print axioms` shows that the imported resolution principle
`AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_exists_mono` and the source
constructibility comparison use only propext, Classical.choice and Quot.sound.
The delivered theorem still transitively uses sorryAx through the existing assigned
`AlgebraicGeometry.Etale.finite_directImage_constructible_and_higher_vanishing`
(node `lem-fin-finite-morphism`, module `Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage`).
That existing sorry is not introduced by this delivery and is the next geometric obligation;
its source, node and complete proof plan already exist.

## No longer needed

Removed the following direct proof-only imports:

- `WeilConjectures.SixFunctors.Finite.Stalk`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence`
- `Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Sheaf.CategoryTheory.CartanEilenbergExists`
- `Sheaf.CategoryTheory.HypercohomologyFirstPage`
- `Sheaf.CategoryTheory.ExactCoupleConvergence`
- `WeilConjectures.CategoryTheory.ExactCoupleConvergence`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LeraySpectralSequence`

The following old direct proof dependencies are unnecessary for the implemented wrapper:

- `lemma-weil-pbc-finite-stalk-formula`
- `lem-weil-pbc-inverse-image-stalk-germ`
- `prop-weil-pbc-geometric-stalks-exact`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `thm-constructible-serre`
- `def-weil-pbc-scheme-conventions`
- `lem-weil-pbc-grothendieck-spectral-sequence`
- `lem-weil-pbc-module-sheaves-grothendieck-abelian`
- `lem-weil-pbc-module-sheaves-enough-injectives`
- `def-weil-pbc-direct-image`
- `lem-sp-cartan-eilenberg-exists`
- `thm-sp-if-e1`
- `def-finrepair-property-c`
- `def-sp-convergence`

The proof uses a finite-order resolution criterion, so the full Cartan--Eilenberg resolution,
hypercohomology spectral sequence and convergence construction are unnecessary. Surjective
pullback faithfulness supplies the already proved unit monomorphism, so the direct finite
stalk formula and inverse-image germ calculation are unnecessary here. Serre closure is
already used inside the proved resolution criterion. The old seven tool approvals are
removed because none is directly used in the new wrapper. No claim is made that all these
modules disappear from the entire targets' closure; some remain transitive source imports.

The current source `FiniteCancellation` wrapper itself is not imported: it depends on the
separate unproved source finite-pushforward theorem. Instead, the proof uses the assigned
finite constructible direct-image declaration and the axiom-clean resolution principle.

The unit `sk-prop-sf-cbc` has no realized statement or proof step assigned to this item.
The compact-support base-change route of the unit and chapter is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG plan duplicates a source-library finite-order
resolution principle and therefore plans more spectral-sequence machinery than is needed.
The direct cancellation source theorem initially looked complete, but axiom inspection
showed its finite-pushforward dependency is still sorry in this tree. The delivered proof
instead retains the stated finite-direct-image dependency from the assigned plan.

Every original assumption remains, including those on S and Y that the resolution principle
does not need. No compatibility of f or pi with the chosen k-structures is used or assumed.
Zero coefficients and empty schemes are covered by the same source APIs. Negative degrees
were checked explicitly. The original API docstring is preserved; inline comments and the
DAG describe the shorter implemented route.

## New nodes

`lem-finrepair-constructible-direct-images-from-embeddings` records the already proved
`AlgebraicGeometry.Etale.hasConstructibleDirectImages_of_exists_mono` in
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage`.
Its statement is the general resolution criterion, without any finite cover, finite-type
or invertible-exponent hypothesis. The node includes the existing exact Lean signature,
source and complete finite-order proof in words. LeanSearch, LeanFinder, Loogle and Mathlib
grep found no matching Mathlib result; direct source search found this proved declaration,
and DAG and blueprint searches found no existing node for it. It creates no Lean module,
statement, definition or sorry. No change record is needed because no interface changed.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
