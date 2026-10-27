## What changed

Completed the remaining target-open comparison in `Sheaf.Paper.MateOpenRestriction` without changing any original theorem signature. The comparison is the conjugate of a normalized compact-support isomorphism under the two composite adjunctions; its stated Hom equation and uniqueness are proved explicitly.

The eight original canonical map definitions are moved verbatim to `Sheaf.Paper.MateOpenRestrictionMaps`, publicly imported by the original module. This breaks the otherwise circular dependency between the maps and their geometric properties. All names, signatures, terms and downstream visibility are preserved. The change record is `coord/changes/mate-open-restriction-maps.md`.

Added proved geometric helpers in `MateOpenProperRestrictionIso`, `MateOpenProperSupport` and `MateOpenCompactSupportExchange`. The first identifies the specified proper/open counit mate with the normalized derived square mate. The second extends boundary vanishing from constructible finite-Tor generators to the entire localizing hull, handling all seven coefficient alternatives, including continuous algebraic-closure coefficients. The third transposes the inverse restriction map, proves its counit invertible by open/closed conservativity, and proves the exact normalization used by the item.

No source-library module is changed. The original three completed proofs remain unchanged. A textual comparison also confirms that all four original theorem signatures and all eight extracted definition bodies are identical to the shared source. The definition extraction has only two external direct consumers, both using `mateOpenTrivialLowerShriek`; their imports continue to expose its identical definition, so no adaptation is required.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.ProEtale.CondensedRing.mateOpenTargetRestriction` (node `det-sf-mate-open-restriction`): 1 of 1 original sorries.

New theorems proved: `mateOpenProperRestriction_isIso`, `mateOpenProperSupport`, and `mateOpenCompactSupportExchange`, each with its own node listed below. No new sorry is added; no hole is split off. All five delivered Lean modules contain zero sorries. Existing imported statements may retain their project sorries; none is edited or newly introduced here.

Validation: an ordered compilation of all five changed modules and both unchanged external consumers completed successfully with no warnings. All original theorem signatures and all eight canonical definition bodies were compared textually with the shared source and are identical. The node overlay is acyclic, and every Lean line meets the 100-character limit. The first complete delivery check passed compilation and the axiom probes; its preflight found only that the maps node recorded the first definition body as part of its signature. That metadata field is corrected to the signature alone, and deliver3.py reruns the required preflight. The unchanged consumer copies were removed from the sandbox after verification; they are not part of the delivery.

## No longer needed

Removed proof imports `Sheaf.Paper.LocalizingLowerShriekComposition`, `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition`, and `Sheaf.Paper.BrownHypotheses`. The target-open proof uses the actual Cartesian compactification and normalized proper/open exchange, so it does not need the general rational or nonrational composition theorems. Brown existence is still used through `BrownExceptionalAdjoint`; the direct Brown-hypothesis import is redundant.

Removed the planned direct dependencies `lem-sfb-localizing-lower-shriek-composition`, `lem-sfb-nonrational-localizing-lower-shriek-composition`, `sk-lem-brown-hypotheses`, `lem-pod-separated-finite-type-base-change`, and `lem-sfb-finite-type-composition-base-change` from this node's proof route and its obsolete top-level tool approvals. The geometric base-change facts are supplied directly by Mathlib instances and the new open-square helper. These dependencies can still be used by other library declarations; no module is withdrawn and no upstream declaration is removed. No unit statement or realized proof step is bypassed. The new support proof also needs no direct import of `ProperOpenComplementSquare`, and the normalized-exchange proof needs no direct import of `DerivedOpenSquareRestriction`; their requisite facts come from the more precise helper declarations.

## Where the brief, the DAG or earlier work was wrong

The retained target-open plan invokes general lower-shriek composition. That route does not directly supply the exact normalization by `mateOpenTargetLowerShriek` required by the Lean signature. Moreover, the existing standard proper/open interchange statement specializes the coefficients to the finite-subextension convention and assumes a dense compactification, whereas this theorem accepts every admissible coefficient and an arbitrary compactification. The proof instead derives the normalized Cartesian proper/open comparison using the existing scalar-square and closed base-change declarations. The continuous algebraic-closure coefficient alternative is handled separately by its existing norm-topological closed base-change theorem.

The new node overlay was checked for cycles through both statement and proof dependencies; none was introduced. The unit's formal mate/conjugation route is preserved. The current unit record has no realized node attachment requiring the discarded general composition dependencies.

## New nodes

`def-sfb-mate-open-restriction-maps` attaches the eight unchanged canonical definitions to `Sheaf.Paper.MateOpenRestrictionMaps`; it records their construction and public reexport. Change record: `coord/changes/mate-open-restriction-maps.md`.

`lem-sfb-mate-open-proper-restriction-iso` attaches `mateOpenProperRestriction_isIso`: normalized derived open-square adjunctions make the specified restriction mate invertible, even without properness or constructibility.

`lem-sfb-mate-open-proper-support` attaches `mateOpenProperSupport`: proper image of open extension has zero restriction to the closed complement on the whole localizing hull.

`lem-sfb-mate-open-compact-support-exchange` attaches `mateOpenCompactSupportExchange`: open transposition and supported counit invertibility yield the left-adjoint comparison with the exact target restriction normalization.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
