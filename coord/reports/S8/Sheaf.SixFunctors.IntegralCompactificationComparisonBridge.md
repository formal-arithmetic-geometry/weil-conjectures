## What changed

`Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` proves
`completedComparison_existsUnique` by applying the constant-coordinate Hom bijection
and proves `comparisons_isIso` by composing the existing open reconstruction,
proper-limit, realization, completion-unit, and normalized word isomorphisms.
Four proved private helpers make the latter argument explicit. Public statements,
public imports, and definitions are unchanged.

The new module `Sheaf.SixFunctors.IntegralConstantCompleteTransport` isolates the
coefficient transport needed by both proofs. This is a decomposition, not two
independent sorry-free proofs. It asserts neither compactification compatibility nor
any word comparison. Its two clauses are the completeness and full-faithfulness
consequences of the general constant-completion equivalence after the published
coefficient and small-site transports.

Change record: `coord/changes/S8-integral-constant-complete-transport.md`.

## Proved and sorry left

Original item: three holes. Closed two original holes:

- `WeilConjectures.IntegralCompactificationBridge.completedComparison_existsUnique`.
- `WeilConjectures.IntegralCompactificationBridge.comparisons_isIso`.

One original hole remains unchanged:

- `WeilConjectures.IntegralCompactificationBridge.integralCompactificationComparisonBridge`
  (`lem-sf-integral-compactification-comparison-bridge`). Its complete nine-step
  natural-language argument remains in the declaration and the node.

One new hole is added:

- `WeilConjectures.GeneratorReduction.integralConstantCompleteTransport`
  (`lem-sf-integral-constant-complete-transport`).

Thus this packet closes two textual upper holes and adds one strictly smaller
coefficient-only obligation: a decomposition with a net reduction of one hole.
The new lemma is not an arbitrary-witness existence statement and constructs no data.
The existing uniquely normalized completedComparison choice is preserved.

## No longer needed

Removed unused private proof imports `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
and `Sheaf.SixFunctors.AmbientProperOpenPasting`; the proved auxiliaries use neither
directly. No public import or node is withdrawn. The final theorem is still open, so all
nine original plan steps and their declared dependencies are retained. None of the
unit's statement or realized steps is bypassed. No source-library declaration is
changed, deleted, or replaced by sorry.

## Where the brief, the DAG or earlier work was wrong

The general constant-completion equivalence is not directly an API for the actual
functor H on sfIntegralConstructible objects: the coefficient quotient-tower and
small-site transports must be checked. The new lemma records exactly that gap.
The existing admissibility predicates supply the finite-Tor membership needed by
open reconstruction effectivity, and the extra system windows are unnecessary for
these auxiliary invertibility conclusions; their signatures are preserved.

The current return file is empty and the item has no rework row. No quarantined
source is removed. Edge checks: zero objects, empty sites, identity or empty opens
use the same complete coefficient categories and canonical maps. The proof uses
whole derived-system maps, never faithfulness of finite evaluation.

## New nodes

`lem-sf-integral-constant-complete-transport` records the coefficient-only
complete-locus and Hom comparison. Its source is Stacks 099I and 099M, whose local
texts were read. The proof records the actual coefficient quotient identifications,
Roos-unit completeness, small-site transport and exact-derived comparison with H.
LeanSearch, LeanFinder/Loogle and Mathlib grep found only generic completion and
fully faithful functor APIs; the source-library and DAG searches found no statement
for this exact fixed transport. Its module has one public named theorem with whole
proof `by sorry`; it does not import the item and creates no cycle.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
