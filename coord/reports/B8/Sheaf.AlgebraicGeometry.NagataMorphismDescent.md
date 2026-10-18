## What changed

Filled the five existing proof holes in
`Sheaf.AlgebraicGeometry.NagataMorphismDescent`, preserving all public signatures,
public imports, definitions and selected stages. Added the proved private helper
`NagataMorphismDescentData.mapAt_transition`: transported chart maps commute with
transition maps because their coefficient-chart composites and base projections do.

Coverage follows from the recorded union equality stage and
`nagataQCOpenEqEventually`, transported through the canonical pullback comparison.
Overlap agreement follows from `nagataMorphismEqEventually` on the recorded
`overlapData`, the transition helper and pullback extensionality. The over-base
property follows from open-cover extensionality and `mapAt_snd`.

Updated the existing node `def-nagata-morphism-descent` with this proof and its
actual dependencies. The current blueprint's affine-chart gluing construction and
unit route are retained. No new modules, nodes, definitions or public statements.

Validation: the complete module compiled through `lcompile.py` in 42.2 seconds.
The delivery dry run additionally compiles and probes the final source. The proof
uses no nonempty chart-family hypotheses and works over a directed preorder;
the auxiliary linear order remains explicit and unrelated to that preorder.

## Proved and sorry left

Closed all five original holes, all attached to `def-nagata-morphism-descent`:

- `AlgebraicGeometry.NagataMorphismDescentData.coefficient_le_stage`.
- `AlgebraicGeometry.NagataMorphismDescentData.base_le_stage`.
- `AlgebraicGeometry.NagataMorphismDescentData.charts_cover`.
- `AlgebraicGeometry.NagataMorphismDescentData.charts_agree`.
- `AlgebraicGeometry.nagataMorphismDescentGluedMap_over`.

Holes left in the item: zero. Holes added: zero. Split-offs: zero.
These are proofs from the existing named dependencies; the dependencies' own
remaining proofs are outside this delivery.

## No longer needed

No import is removed and no module is withdrawn: the existing public imports
supply the unchanged data-record signature and its exposed construction API.

The proof does not separately use `lemma-nagata-filtered-colimit-finite-data`,
`lem-weil-pbc-limit-global-sections-colimit`,
`lem-pc-filtered-colimit-commrings-elementwise`, or
`lemma-nagata-qc-open-descends`. Their roles are already recorded by the explicit
choice data, notably `unionLimit_eq`, `localMap`, `mapAt_fst`, `mapAt_snd` and
`overlapData`. They remain statement/construction dependencies where appropriate;
this delivery does not claim that their modules leave the targets' import closure.
The old blueprint's unused `def-nagata-affine-fp-descent` route is not introduced.

## Where the brief, the DAG or earlier work was wrong

The existing node's top-level proof and proof dependencies were empty even though
its Lean module had five proof obligations. They now describe the actual proof.
The coverage and overlap docstrings describe earlier construction steps in greater
detail than these proofs require: the record already contains the union equality
and overlap equality data. No mathematical statement or definition needed repair.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
