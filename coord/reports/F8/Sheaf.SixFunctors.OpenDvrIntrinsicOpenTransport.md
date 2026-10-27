## What changed

Proved `WeilConjectures.openDvrIntrinsicOpenTransport` in its existing module, with its
statement and public import unchanged. Added five proved private helpers: preservation
of countable products by the recorded extension, the finite projection of the uniformizer,
compatibility of that section with the recorded coefficient restriction, compatibility of
the scalar chain map with extension, and preservation of quotient completeness.

The proof uses the existing `openDvrIntrinsicCriterion` at the source and target. Between
these applications it gives the principal-completion argument directly for the actual
`O.modules.functor` and `O.extension.ordinary`. It uses the proved `complete_iff_local`,
`complete_iff_principalUnit`, and `principalMapIso` helpers through a proof-only `import all`
of `CompletedDirectImagePreservesCompleteness`. The product comparison uses the existing
proved `proEtaleRingedExtensionByZero_products` at index `ULift ℕ`, followed by equivalence
of discrete index categories. The scalar-projection calculation is the elementary
constant-to-limit calculation also used in `IntegralOpenExtensionComplete`; reproducing
that small calculation locally avoids importing its unrelated open-system structures and
its independent-universe product obligation.

All additional imports serve proofs only. The instance adjustments are scoped to the
private completeness helper: removal of
`CompletedCoefficientPushforward.modAbelian`, `IntegralOnSlice.abSheafify`, and
`IntegralOnSlice.abLocallyBijective` avoids ambiguous independent coefficient universes
when applying those interfaces with equal universes. The existing specific DVR instances
supply sheafification and the locally bijective criterion. No shared interface,
definition, existing module outside the item, or target statement changes. Updated the
item's own DAG proof, proof dependencies, and proof origin to describe this route.

## Proved and sorry left

Closed: `WeilConjectures.openDvrIntrinsicOpenTransport`
(`lem-sf-open-dvr-intrinsic-open-transport`), the item's sole original hole.

Holes closed: 1. Holes added: 0. Holes left in delivered Lean: 0. Split-off statements: 0.
Validation: the delivered module compiled cleanly with `lcompile.py` in 13.4 seconds,
with no warnings. The theorem signature and its node attachment are textually unchanged;
the file has no `sorry` tokens and no lines over 100 characters. The new DAG proof
dependencies have no path back to the item.

All five new private helpers have complete proofs. The proof uses existing declarations
as permitted by stage 3; in particular, the existing hole in
`WeilConjectures.openDvrIntrinsicCriterion` is outside this delivery and is not claimed
proved here.

The argument includes an empty or identity open, the zero complex, and arbitrary unbounded
complexes: no step imposes nonemptiness, a cohomological bound, a characteristic condition
on the schemes, or invertibility of ell on their global sections.

## No longer needed

No original import is removed: `OpenQuotientKoszulModels` remains the public statement
import. The proof does not import `CompletedOpenExchangeTransport` or call
`completedOpenExchangeComparison`; remove
`lem-cbc-completed-extension-zero-comparison` from this node's direct proof dependencies.
It also does not directly call `koszulReconstruction`, so
`prop-weil-pbc-koszul-reconstruction` leaves the direct proof dependencies. This latter
node remains a statement dependency and an indirect dependency of the existing intrinsic
criterion; no global withdrawal or elimination of that mathematics is claimed.

The intermediate `IntegralOpenExtensionComplete` import and the independent-universe
product theorem are unnecessary for this route and are absent from the final direct
imports. No existing module or DAG node is withdrawn. The blueprint unit route remains
unchanged.

## Where the brief, the DAG or earlier work was wrong

The old plan's large coefficient-universe and completed-exchange transport is unnecessary
for this assertion once the existing intrinsic DVR criterion is used. The required open
preservation argument can instead be carried out on the fixed completed-integral module
categories by exactness, countable products, and compatibility with the actual uniformizer
section. This is a shorter route below the unit level, not a statement repair.

The existing theorem docstring records the original completed-exchange plan; the updated
DAG and the proved private helpers record the implemented principal-completion argument.
No mathematical error in the assigned statement was found.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
