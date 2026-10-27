## What changed

Proved `AlgebraicGeometry.ProEtale.StrictTower.singleAlpha_vertical` by restricting
along the top open immersion, applying single-square alpha normalization, and
using inverse-image compositor coherence and naturality. The existing tower,
complex and derived transport proofs are retained. The item's public signatures
and public import are unchanged.

Added `Sheaf.AlgebraicGeometry.SingleAlphaRestrictionNormalization`. Its proved
`singleAlpha_restriction` calculates the restriction of the original intrinsic
cartesian-beta/clopen-projector construction, with all open units explicit.
Added `Sheaf.CategoryTheory.ProperOpenCompositeTransformation`, which evaluates
that functorial word and supplies private proved categorical cancellation lemmas.
A proved equality of whole natural transformations precedes taking components;
this avoids expensive kernel conversions beneath component projections. The
original `singleAlpha` definition is unchanged. No other existing Lean module is
changed.

Restriction detection uses the source-library instance
`mono_upperStarLowerStarAdjunction_unit_app_openImmersionLowerShriek` from
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.LocalVanishing`,
transported through the fixed-coefficient module equivalence. All new imports in
the item are private proof imports.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.ProEtale.StrictTower.singleAlpha_vertical`
(node `lem-cbc-proper-open-alpha-vertical-modules`).

The new `AlgebraicGeometry.ProEtale.StrictTower.singleAlpha_restriction` and
`CategoryTheory.Functor.properOpenCompositeTransformation_app`, the generic
constructor, and every private helper are proved. No holes added or split off.
No `sorry` remains in the three delivery modules. Imported project lemmas retain
their existing proof status.

Validated with `lcompile.py`: the generic word module compiled in 2.7 seconds,
the normalization module in 17.7 seconds, and the assigned module in 36.1 seconds.
The unchanged direct consumer `Sheaf.AlgebraicGeometry.ProperOpenAlphaPasting`
compiled against the delivery in 17.0 seconds; its temporary copy was removed.
The normalization proof passed with a deliberately lowered diagnostic heartbeat
budget. All diagnostic options and output commands have been removed. The delivery
tool checks the final files again.

## No longer needed

No original import was removed and no module is withdrawn. The parent node's
explicit image/open-closed argument, and its direct proof dependency on
`lem-weil-pbc-proetale-ringed-open-closed`, are unnecessary: the existing
source-library monic-unit instance detects restriction directly. This does not
claim that the ringed open/closed module is globally unused.

The beta-normalization, clopen-projector and proper/open arrow nodes remain
needed through the proved single-square normalization module. No dependency is
pruned merely because its declaration has an unfinished proof. The unit route
is retained.

## Where the brief, the DAG or earlier work was wrong

The planned mathematical argument is valid. Directly unfolding ordinary alpha
under a component projection produces an expensive kernel conversion. An
explicit equality of whole transformations, followed by component congruence,
resolves this without changing any shared definition. The source library also
provides the shorter restriction-detection argument used here.

The blueprint ancestor command returns `None` because the parent was created
with a module name rather than a node id. The new node follows its recorded
ancestor, `thm-cbc-complete-proetale`. I read its current proof in
`literature/blueprint/latest/`: the relevant formula is the inverse
open-base-change arrow and the following naturality sentence. The parent's old
stored quotation about completed-map compatibility is absent from that current
proof. No blueprint or unit statement changes.

## New nodes

`lem-cbc-single-alpha-restriction-normalization` records the single-square
restriction formula. It is a strict step of the vertical argument. Searches in
the DAG, Lean library and current blueprint found no existing exact statement;
the actual Mathlib `leanfinder`, `loogle` and `grep` queries are in
`searches.jsonl`. Existing adjunction compositor/unit APIs are reused. Empty
opens, identity opens and the zero coefficient ring need no extra hypotheses.

`lem-cbc-proper-open-word-components` records the generic constructor and its
proved component formula. It retains all associators and comparison maps of
the original word. The proof uses Mathlib whiskering and associator component
lemmas; actual searches are recorded. It has no geometric or finiteness
hypotheses and covers empty categories. The normalization module imports its
private categorical calculations with `import all`.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
