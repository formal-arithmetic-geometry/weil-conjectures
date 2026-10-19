## What changed

Proved both bounded standard t-structure existence-and-uniqueness theorems in
`Sheaf.Paper.SfConstructibleHeart`, preserving every existing statement and definition.
The retained rational proof induces the integral t-structure, descends it through scalar
localization, proves orthogonality by tensor induction, localizes truncation triangles,
transfers bounds, and proves uniqueness from the prescribed classes.

Completed the retained auxiliary module `Sheaf.Paper.SfIntegralStandardTruncations`.
Finite type supplies noetherianity and finite dimension, and the specified finite-field
cardinality supplies prime invertibility. The existing stratified-perfect characterization
gives bounds and truncation closure after exact coefficient restriction. Faithfulness
reflects boundedness; the exact-functor truncation comparisons transport membership back.
No completed-coefficient equivalence needs to be chosen for this proof.

The common-stage proof uses the published ordinary-to-completed scalar comparison to
preserve both degree classes. Each morphism between opposite classes has a representative
at one finite common field, where rational orthogonality makes it zero. Exact finite-stage
inclusions supply truncation triangles; each object's own stage supplies bounds.
Shift comparisons prove shift closure, and prescribed class functions prove uniqueness.
The existing two heart-property proofs are retained unchanged.

All added imports in the existing item are proof-only. No existing signature, definition,
public import, target statement, or consumer module changes. DAG proof records follow
these proofs.

## Proved and sorry left

Closed both of the 2 holes present at dispatch, node `def-weil-constructible-heart`:

- `WeilConjectures.sfRationalStandardTStructure_existsUnique`.
- `WeilConjectures.sfCommonStageStandardTStructure_existsUnique`.

The auxiliary `WeilConjectures.sfIntegralStandardTruncations`, node
`lem-sf-intrinsic-integral-standard-truncations`, is also proved in this session.
Holes added: 0. Sorries left in either delivered module: 0. No unproved result is split off.
Existing dependency theorems remain the intended stage-3 premises.

## No longer needed

No existing public imports, nodes, or globally reachable modules are removed.
The retained attempt's proposed dependence on
`def-pur-completed-coefficient-presentation-transport` is unnecessary: the landed
`integralDetailedTransport` already is exact coefficient restriction, and the source
library supplies its truncation comparisons and boundedness reflection. That proposed
proof dependency and import are removed from the auxiliary theorem's plan.
The legacy rational/common-stage heart existence declarations are unused because their
coefficient presentations differ. `ConstructibleTruncations` is not imported: its
interface imports this item and would create a cycle. The common-stage proof uses the
existing representative calculus directly and needs no new functor-descent lemma.

## Where the brief, the DAG or earlier work was wrong

The retained attempt left the integral auxiliary theorem and common-stage existence open.
Both are now proved from existing declarations. The original item node had no numbered
proof steps; its theorem docstrings and the standard-pair node supply the construction.
The unit `sk-def-sf-admissible` records no realized statement or proof steps for this node,
so the proof changes bypass no required unit step.
The two heart-properties proofs had already landed before dispatch and are not counted.
No statement repair or forced consumer adaptation is needed.

## New nodes

`lem-sf-intrinsic-integral-standard-truncations`, in
`lean/Sheaf/Paper/SfIntegralStandardTruncations.lean`, records the integral boundedness
and good-truncation lemma used by the rational proof. It is strictly the integral step,
with no rational category or t-structure existence conclusion, and is proved here.
Its source is Bhatt--Scholze Proposition 6.8.11(3); its node and docstring give the proof.
No change record is needed because existing interfaces are unchanged.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
