## What changed

Proved `AlgebraicGeometry.isIntegral_affineGroupoid_invariants` from the two declarations
in the current DAG: `affineGroupoid_rankwise_monic_gluing` and
`affineGroupoid_constantRank_norm_annihilator`. The target statement and public imports
are unchanged. All edits are in the assigned module and its own DAG node.

Three proved private helpers supply the interface between these declarations:
`groupoid_transport` transports every groupoid law through object and arrow isomorphisms;
`degree_specMap` preserves finite local freeness and fibre degree under the canonical
affine spectrum isomorphisms; `constantRank_sections_equation` applies the norm lemma to
the section rings and lifts its monic polynomial into the equalizer subring. Injectivity
of the inclusion reflects monicity, and mapping preserves the degree and evaluation.
The main proof chooses these local equations and applies the existing gluing conclusion.
When the rank index set is empty, the covering equality forces the spectrum empty,
and the gluing declaration supplies the polynomial `X`.

Read Stacks `groupoids.tex`, `lemma-finite-locally-free-disjoint-free` and
`lemma-integral-over-invariants` (Tags 03BI and 03BJ). The proof follows both paragraphs
of 03BJ. The node now describes the explicit affine-spectrum transport and polynomial
lifting needed between its original steps. Its two proof dependencies are unchanged.
A LeanFinder search for integrality over the equalizer of finite locally free groupoid
maps returned only general integral morphism results; local searches found the two
planned statements as the applicable interfaces. Loogle's query `"IsIntegral", "invariant"`
returned the finite/profinite abstract group action results, which do not cover this
groupoid. The grep query `groupoid.*integral|integral.*invariant|invariant.*integral`
likewise found group-action integrality and unrelated analytic integral results.

Validation: the delivered module compiled through `lcompile.py` in 13.4 seconds,
exit code 0, with no warnings. The public statement and public import list were
also compared with the current source and are unchanged. Every Lean line is at most
100 characters; the node JSON parses successfully.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.isIntegral_affineGroupoid_invariants`
(node `lem-a1-affine-groupoid-integral-invariants`). No hole remains in the delivered
module and no hole is added. All three private helpers are proved completely.

The two existing dependency declarations remain separate tasks, as the stage-3 brief
intends; this delivery neither changes nor adds their holes. This is a proof from
existing stated dependencies, with no new decomposition.

## No longer needed

Removed these direct proof imports:

- `Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections`
- `Mathlib.Topology.Sheaves.CommRingCat`
- `Sheaf.AlgebraicGeometry.AffineGroupoidInvariantRankStrata`
- `Sheaf.AlgebraicGeometry.AffineGroupoidPolynomialNormInvariant`
- `Sheaf.RingTheory.FiniteLocallyFreeNormCharacteristicPolynomial`

Their uses belong inside the two planned dependencies, which retain the necessary
transitive imports. No dependency node or module is claimed globally unnecessary;
no mathematical route or unit step is pruned. Both current DAG proof dependencies
are used, and no public import is removed.

## Where the brief, the DAG or earlier work was wrong

The item's old direct proof imports and six-step docstring predate the approved
two-dependency DAG split. The existing statements are sufficient, but assembling them
also requires transporting a groupoid on affine open subschemes to spectra of their
section rings. This bridge is now proved locally rather than postponed as another
statement. No statement, definition, shared interface, or source-library file changes.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
