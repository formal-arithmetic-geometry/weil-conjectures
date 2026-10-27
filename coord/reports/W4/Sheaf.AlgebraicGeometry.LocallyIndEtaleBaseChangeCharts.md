## What changed

Filled `AlgebraicGeometry.locally_indEtale_base_change_charts` in the assigned
module, keeping its complete signature unchanged. Proved private helpers identify
the equal-universe `IndEtaleAcrossUniverses` predicate with `RingHom.IndEtale` and
apply the source-library base-change theorem to the right tensor inclusion.

For fixed charts, `pullback.map` is an open immersion with exactly the required
intersection as range. `IsOpenImmersion.isoOfRangeEq` constructs the comparison;
the tensor-spectrum projection formulas give both equations, and cancellation of
the two open immersions followed by `pullback.hom_ext` proves uniqueness.
For arbitrary pullback points, choose an affine open inside the inverse image of
the base chart, factor its map through that chart, recover the ring map with
`Spec.preimage`, and use the tensor spectrum as the new affine chart.

The item's node now records these concrete APIs. No shared interface, definition,
statement, target, other module, or unit route changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.locally_indEtale_base_change_charts`
(`lem-trf-locally-ind-etale-base-change-charts`).
Added zero holes; zero holes remain in this delivery. There are no split-off
statements. The two private helpers have complete proofs.

Validation: the complete file compiled through `lcompile.py` without errors or
warnings in 5.5 seconds. A textual comparison confirmed the original theorem
signature is identical, and all Lean lines have at most 100 characters.

## No longer needed

Removed the redundant private import `Mathlib.AlgebraicGeometry.AffineScheme`,
already public through `Mathlib.AlgebraicGeometry.Pullbacks`.
Removed the private import `Sheaf.RingTheory.IndEtaleStability`: only ind-etale
base change is needed, already proved as
`RingHom.IndEtale.isStableUnderBaseChange` in the adopted source library and
available through the existing public definition imports. Its principal-Zariski,
composition, filtered-colimit, relative and weakly-etale clauses play no role.
The mathematical dependency `lem-weil-pbc-ind-etale-stability` is retained for its
base-change clause; no DAG node is withdrawn. No other imports or mathematical
steps are pruned, and no claim is made that the removed module has no other users.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The existing declarations suffice for both
conclusions, including the canonical projection equations. The proof needs no
separation or finiteness assumption. Empty pullbacks are covered by the pointwise
quantifiers; no nontrivial-ring assumption is used, so zero tensor rings are
allowed. The isomorphism is unique relative to the fixed presentations because
their maps into the ambient schemes are monomorphisms.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
