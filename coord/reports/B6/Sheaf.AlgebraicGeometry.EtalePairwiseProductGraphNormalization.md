## What changed

Proved `AlgebraicGeometry.Etale.EtaleGraphPresentation.PairwiseProduct.b_projections`
and `AlgebraicGeometry.Etale.EtaleGraphPresentation.PairwiseProduct.geometry` in
`Sheaf.AlgebraicGeometry.EtalePairwiseProductGraphNormalization`.
The projection equations simplify the literal `pullback.map`. The geometry proof uses
Mathlib's `MorphismProperty.pullbackMap`, cancellation of open immersions,
proper base change and composition, and `IsProper.of_comp` for the product graph and
both neighborhood graphs. The product graph is proper directly because its composite
with the separated first projection is the given proper `s.a`.

Updated the node's first proof step and proof origin to reflect this shorter geometric
argument. All statements, definitions and public imports are unchanged. Removed the
redundant private import of `Sheaf.SixFunctors.EtaleLocallyClosedGraphModel`, which is
already publicly imported by `EtaleGraphComparisonBaseChange`.

## Proved and sorry left

Closed 2 of the module's original 3 holes:

- `AlgebraicGeometry.Etale.EtaleGraphPresentation.PairwiseProduct.b_projections`.
- `AlgebraicGeometry.Etale.EtaleGraphPresentation.PairwiseProduct.geometry`.

The one remaining hole is
`AlgebraicGeometry.Etale.etalePairwiseProductGraphNormalization`, attached to
`lem-pur-etale-pairwise-product-graph-normalization`. Its complete original statement
and sourced natural-language proof remain in place. The triple-product coherence
calculation in steps 2–10 is still unformalized. This is a partial proof delivery,
with no split-off statements and zero added holes.

The completed geometry and projection proofs compile cleanly with `lcompile.py` (6.6 s).
The delivery preflight additionally checks the resulting axioms and declarations.
No added hypotheses are used: empty sources, repeated presentations, non-quasi-compact
supporting opens and arbitrary base schemes are included.

## No longer needed

Removed the redundant private import `Sheaf.SixFunctors.EtaleLocallyClosedGraphModel`.
Its module remains transitively imported and is still needed for the definition of the
specified graph comparison. No node or module is withdrawn or claimed pruned.
The geometric proof avoids the identity-top Cartesian-square argument for properness
of `a`, using proper-to-separated cancellation instead. All declared dependency nodes
remain relevant to the full comparison proof; none is removed from the DAG.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The first geometric step has a shorter proof in Mathlib than
the planned pullback argument. `EtaleGraphComparisonInterchange` cannot be used to close
the main identity: its DAG proof depends on this item, even though the unfinished Lean
proof does not yet import it. The existing Noetherian compact-support formalism has
extra hypotheses and does not establish the arbitrary-scheme identity here.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
