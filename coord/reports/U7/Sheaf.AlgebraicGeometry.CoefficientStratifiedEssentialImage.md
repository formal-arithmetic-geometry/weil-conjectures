## What changed

Implemented `AlgebraicGeometry.ProEtale.coefficientFixed_essImage_of_stratification`
without changing its statement. The proof follows the actual finite-stratum induction
of Stacks Project, proetale.tex, Tag 09AK, and the current blueprint unit's proof.
It chooses affine neighborhoods where the selected stratum is closed with
quasi-compact complement, pulls back the stratification twice, deletes the empty
selected stratum using `Fin.succAbove`, and applies strong induction.

The private helpers `fixedComp`, `fixedComparisonPullback`, `fixedOrigin_pullback`
and `fixedOrigin_strata_pullback` construct and apply the canonical inverse-image
isomorphisms using sectionwise direct images and adjunction conjugation. The private
`eraseEmptyStratum` retains the actual domain schemes and immersions of every other
stratum. There is no arbitrary choice of a mathematical object from a sorried theorem.

Two genuine steps of the source argument are isolated in new theorem modules:
Zariski locality of etale origin, and gluing over an affine scheme from a
complementary closed immersion and quasi-compact open immersion. Their independent
coefficient universes are essential. They are proof-only imports of the item, as
are the existing stratification-pullback and affine-neighborhood tools.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.coefficientFixed_essImage_of_stratification`
(node `lem-pe-coefficient-stratified-essential-image`) by a complete Lean induction
from the two new descent statements. No `sorry` remains in the item module; its
private transport and finite-partition helpers are all proved.

Added two holes, each the entire proof of a public named theorem in its own module:

- `AlgebraicGeometry.ProEtale.coefficientFixed_essImage_of_openCover`, in
  `Sheaf.AlgebraicGeometry.CoefficientOriginOpenCover`, node
  `lem-pe-coefficient-origin-open-cover`.
- `AlgebraicGeometry.ProEtale.coefficientFixed_essImage_affine_openClosed`, in
  `Sheaf.AlgebraicGeometry.CoefficientOriginAffineOpenClosed`, node
  `lem-pe-coefficient-origin-affine-open-closed`.

This is a decomposition: one upper hole closed and two strictly smaller argument
steps added, rather than an unconditional proof. The locality theorem contains no
stratification. The second theorem treats only a single complementary open-closed
pair on an affine scheme; it contains neither finite-partition induction nor
Zariski localization. Both include a source and a complete proof in words.

Edge cases checked against the argument: zero strata force an empty base and give
the empty open cover; empty strata can be erased while retaining the cover; the
complement may be empty; and a closed immersion with full underlying image need
not be an isomorphism. Neither new statement adds finite generation, finite stalks,
Noetherian coefficients or quasi-compactness of the original scheme. Arbitrary
module-valued restrictions are retained.

## No longer needed

No existing import was removed: the original public import supplying the
statement's sites, functors and stratifications is unchanged.

The original planned direct dependency
`lem-weil-pbc-comparison-stratified-essential-image`, module
`Sheaf.Paper.ProEtaleStratifiedEssentialImage`, is not imported or applied by this
proof. Its theorem fixes both the coefficient ring and module universe to `u+1`,
so it does not instantiate at `max v (u+1)` for a general independent `v`. Its proof
was used as an implementation reference, not as a black box. The parent node's
proof dependencies now name the actual two coefficient-sized descent steps and
the already proved affine-neighborhood lemma. No original-site module is
withdrawn or claimed to be globally unused; its other consumers remain intact.

## Where the brief, the DAG or earlier work was wrong

The DAG described the coefficient-sized theorem as obtained by transporting the
original stratified theorem along AsSmall equivalences. Those equivalences change
the site presentation, not the coefficient category's Hom universe. The existing
original-site theorem requires `A : Type (u+1)` and `ModuleCat.{u+1} A`; its
underlying geometric APIs have the same constraint. It therefore cannot be
specialized to an arbitrary `A : Type (max v (u+1))` just by transporting the sites.
The item statement itself is valid and unchanged. This packet implements its
finite-partition induction, keeping only the actual coefficient-size gaps as
separate locality and affine open-closed gluing statements. The blueprint unit's
route is preserved.

## New nodes

`lem-pe-coefficient-origin-open-cover` is the Zariski-locality step at the start
of Tag 09AK's proof. Its new module is
`lean/Sheaf/AlgebraicGeometry/CoefficientOriginOpenCover.lean`. Its argument tests
the comparison counit on the cover, using compatibility with open restriction
and full faithfulness, and then recovers an etale antecedent globally.

`lem-pe-coefficient-origin-affine-open-closed` is Tag 09AK's complementary
open-closed exact-sequence step, with Tag 09AH providing that sequence. Its new
module is `lean/Sheaf/AlgebraicGeometry/CoefficientOriginAffineOpenClosed.lean`.
The end terms descend by extension-by-zero and closed-direct-image comparison;
extension closure supplies the middle term. Both nodes record LeanSearch,
LeanFinder and grep searches. There are no definition/signature repairs and no
change records or forced consumer adaptations.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
