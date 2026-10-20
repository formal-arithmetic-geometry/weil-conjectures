## What changed

Withdraw `Sheaf.AlgebraicGeometry.FinitePresentationLocalObjectModels` as an unused
duplicate, using `deleted.txt` (brief step 8d). Its source counterpart already
proves `AlgebraicGeometry.exists_finitePresentation_local_object_models` with
the same conclusion and without the Noetherian ring hypothesis. Reattach
`lem-pc-fp-local-object-models` to that unchanged upstream declaration, recording
its actual signature. Keep the node's mathematical statement and proof plan.

The proof route remains the finite affine cover, chart object models, a common
upper bound, and pullback transport in the existing node. The unit record
`sk-thm-picard-semicon` has no realized attachment for this auxiliary node;
no unit statement or step is bypassed. Read Stacks `limits.tex`,
`lemma-descend-modules-finite-presentation`, first proof, which reduces to the
affine case and Zariski gluing without a Noetherian hypothesis.

Change record: `coord/changes/D9-retire-finite-presentation-local-object-models.md`.
No adopted source declarations, signatures, attributes, imports or proofs change.

Validation: server compilation through `lcompile.py` of a scratch module importing
only the upstream module proves the exact old signature by direct application.
It compiles cleanly in 5.8 seconds. `#print axioms` for the retained theorem reports
only `propext`, `Classical.choice`, and `Quot.sound`. A source-wide import search
and `tools/downstream.py` both find zero importers of the withdrawn module.
LeanFinder returns generic finite-presentation sheaf lemmas, not this descent
statement; Loogle does not index this project declaration. The local source search
finds the retained stronger theorem and its existing local-descent-datum consumer.

## Proved and sorry left

The assigned module has zero holes at the delivery base: 0 closed, 0 added,
0 split off, and 0 remaining. This delivery prunes an already proved duplicate;
it does not claim a newly closed hole. The retained upstream theorem
`AlgebraicGeometry.exists_finitePresentation_local_object_models` has a complete
proof with only the three permitted axioms, and its direct specialization proves
the withdrawn module's original statement. There are no remaining or added
`sorry` declarations in the packet.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.FinitePresentationLocalObjectModels`.
Its duplicate public theorem and private `transport_chart_model` helper are
withdrawn together. Its former consumer is already the unchanged upstream
`WeilConjectures.AlgebraicGeometry.FinitePresentationLocalDescentDatum`, importing
the upstream counterpart. No consumer adaptations are needed.

All imports of the withdrawn module disappear with it:

- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.RingTheory.Noetherian.Basic`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit`
- `WeilConjectures.AlgebraicGeometry.FinitePresentationAffineChartModels`
- `Mathlib.Data.Finset.Order`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`

Those modules themselves remain needed by the retained source proof or other
consumers; none is proposed for withdrawal. The mathematical node
`lem-pc-fp-local-object-models` remains and now points at the source declaration.
Its dependency `lem-pc-fp-affine-chart-object-models` remains used. No mathematical
node or source-library dependency is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The brief describes a holed module, but this module already contains a complete
proof and is unused. The DAG attachment still points at this duplicate even
though the upstream theorem and upstream consumer already provide the route.
The retirement census listed the two signatures as different because the source
version omits the unused Noetherian instance assumption. They need not be textually
identical: the source statement directly specializes to the old node statement,
verified by the compiler. No statement repair or new lemma is necessary.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
