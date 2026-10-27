## What changed

Filled `AlgebraicGeometry.ProEtale.ClosedFiniteTransport.closedFiniteAdjointCounitTransport`
without changing its statement or any definition. Added the private proof import
`Sheaf.CategoryTheory.ExactAdjointClassicalCounitComparison`.

The proof transports the existing compact-support adjunction along `compactSupportIso`,
uses Mathlib's `rightAdjointUniq_hom_app_counit`, and supplies exact-functor bounds via
`termwiseIso` to `DerivedCategory.exactAdjoint_classicalCounitComparison`. That existing
lemma supplies the bounded-below support value and a natural alpha. The isomorphism
identity `Iso.hom_eq_inv` identifies its inverse with `comparisonUnitIso.inv`.
The two specified formulas for the lemma's natural counit combine to the required
`transportedCounit` equality by transitivity. Its source is definitionally the existing
`sfFiniteExceptionalAt` composite.

Updated the theorem node's proof, proof dependencies and origin to match this assembly.
Removed only obsolete top-level tool approvals; statements, attachments, definitions,
public imports, and the unit route stay as before. No other module is changed.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.ProEtale.ClosedFiniteTransport.closedFiniteAdjointCounitTransport`
(node `lem-pur-closed-finite-adjoint-counit-transport`).

Holes closed: 1. Holes added: 0. Sorries remaining in the delivered module: 0.
No split-off statements. This is a proof from existing declarations, not a decomposition.

Validation: the delivered module compiles cleanly through `lcompile.py` in 20.1 seconds.
All Lean lines satisfy the 100-character limit. The added import passes the project
import-direction check.

## No longer needed

Removed unused private imports:

- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`
- `Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.CategoryTheory.Localization.Predicate`

The proof does not need `lem-pur-closed-unbounded-compact-support-normalization`
(`Sheaf.AlgebraicGeometry.ClosedUnboundedCompactSupportNormalization`): its required
identifications are already constructed in the item, and the source library's proved
exact-functor bound API supplies the bounds directly. It does not need
`lem-pur-closed-transported-hom-counit-formula`
(`Sheaf.AlgebraicGeometry.ClosedTransportedHomCounitFormula`): the statement uses an
explicitly defined composite `transportedCounit`, and both of its comparison formulas
come directly from the categorical lemma with the item's `closedComparison`.
These dependencies were never imported into the item and are removed from its DAG route.

The canonical compact-support site comparison (`lem-sf-class-compact-support-comparison`),
the separate oriented-localization theorem (`lem-trf-oriented-closed-base-localization`),
and the bounded derived direct-image comparison theorem
(`sk-thm-pe-direct-image-comparison`) are not used by this proof. Their obsolete
top-level tool approvals are removed. `closedComparison` still uses the actual underived
comparison mate and its invertibility from the source library; that construction is
unchanged. The actual unbounded-derived unit theorem from the source library replaces
use of the wrapper `CompactSupportComparisonUnit`.

No module is withdrawn. These are dependencies no longer needed by this item; no claim
is made that they have no other consumers. All original public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The planned geometric normalization and relative Hom-bijection lemmas are stronger than
what the existing Lean statement needs. The supplied definitions already fix the exact
normalizations and define the transported counit, so the stated categorical comparison
lemma suffices for assembly. This changes no mathematical statement or unit step.

Searches through leanfinder, loogle and grep found Mathlib's right-adjoint uniqueness
counit equation; source search found the existing proved exact-functor lower/upper-bound
API. The existing categorical lemma was checked against all three conjuncts. The
argument uses no extra hypotheses and applies also to zero objects, identity or empty
closed immersions, and arbitrary shifts within D+.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
