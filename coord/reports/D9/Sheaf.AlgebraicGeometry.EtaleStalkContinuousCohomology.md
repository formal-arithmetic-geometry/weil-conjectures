## What changed

Retired the assigned zero-hole duplicate module and listed it in `deleted.txt`.
Change record: `coord/changes/D9-retire-etale-stalk-continuous-cohomology.md`.
The sole direct consumer, `Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding`,
now imports the adopted source comparison and constructs its embedding as the inverse of the specialized
`sheafHAddEquivContinuousCohomology` equivalence. The item node and the consumer node were updated to record this route.

## Proved and sorry left

The item contained zero `sorry`s before retirement and zero afterward. Closed 0
of 0 holes; added 0 holes; split off 0. No `sorry` remains in delivered modules.
The adopted source additive equivalence is complete and its inverse `.toEmbedding`
is checked by Lean.

## No longer needed

The duplicate `Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology` module and
its imports of the abelian stalk equivalence, global-sections comparison, Galois
extension lemma, derived evaluation, and duplicate discrete-invariants comparison
are pruned. The forward consumer no longer imports the stalk-galois module or the retired stalk
theorem; it uses the adopted source stalk comparison and units Galois-point stalk API.

## Statement corrected

The node now records the adopted source declaration `sheafHAddEquivContinuousCohomology` as its statement. The old statement described the retired duplicate theorem `nonempty_equiv_etale_cohomology_continuous_stalk`, with an arbitrary algebraic closure and a `Nonempty` equivalence. The source module provides the canonical additive comparison at `galoisPoint`; the duplicate module is withdrawn and the consumer uses the source comparison directly. The source is `lean/WeilConjectures/AlgebraicGeometry/EtaleStalkContinuousCohomology.lean`, in the declaration `sheafHAddEquivContinuousCohomology`.

- `lem-sc-etale-units-h2-forward-embedding`: holds false for the old proof route; the delivered consumer replaces that route with the adopted source comparison.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a holed theorem, while this assignment is an approved
`retire` item with zero holes. The source twin does not have the old stalk theorem's
signature; it supplies a stronger additive Brauer/Galois equivalence. Its inverse
is sufficient for the sole consumer, so retaining or restating the duplicate would
serve no remaining proof route. No target statement is changed.

## New nodes

None.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
