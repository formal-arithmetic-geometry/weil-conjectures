## What changed

Proved the assembly of WeilConjectures.relativeKunneth from the existing
presentation and coefficient/proper factor lemmas and two independent remaining
steps. The six factors are composed in their original order. Component
invertibility and naturality follow from the existing natural isomorphism.
Coefficient compatibility pastes six CommSq equations. Proper normalization
uses an explicitly constructed identity coefficient comparison; conjugated
proper factors cancel in the composite. Geometric base change pastes six
individual transported factor squares, with their specified source and target
comparisons.

Extracted all existing construction declarations verbatim into
Sheaf.Paper.RelativeKunnethConstructions, publicly reexported by the original
module, to let the two new lemmas state their interfaces without an import cycle.
Change record: coord/changes/A4-relative-kunneth-constructions.md.

## Proved and sorry left

Closed the original direct hole in WeilConjectures.relativeKunneth (1 of 1).
Added two public named holes, each in its own module:

- WeilConjectures.relativeKunneth_cube_factor_transport —
  lem-sf-relative-kunneth-cube-factor-transport. Supplies the seven comparisons
  and six individual equations, without a composite equation.
- WeilConjectures.relativeKunneth_closed_fibre —
  lem-sf-relative-kunneth-closed-fibre. Only the independent absolute
  closed-subscheme specialization, without naturality or compatibility clauses.

This is a decomposition: 1 original hole closed, 2 smaller holes added, net -1.
No sorry remains in the main theorem or any definition. Neither new lemma is the
original theorem with renamed hypotheses. The combination of the six square
identities is written in Lean in the main module.

## No longer needed

The main module no longer directly imports RelativeProductInputDomains,
PointFibreDerivedTensor, DerivedPullbackTensorIso, or FiniteTorStability.
Input-domain and point-tensor obligations are confined to the precise split
steps that use them. The construction owner still receives its canonical tensor
comparison definitions from RelativeProductFactors. ClosedImmersion and Proper
remain direct construction imports; SupportCohomology and
CommonStageCompactWeilCohomology retain their original public visibility.

No original mathematical dependency is claimed globally pruned: the two new
lemmas retain the input-domain, base-change-factor, point-tensor, pullback-tensor,
and closed-immersion ingredients of the unit route. Parent direct proof_deps now
name coefficient-factor-squares and the two new steps. Removed the parent's
obsolete direct tool_uses for finiteTor_stability and derivedPullbackTensorIso;
their relevant content remains below the new steps. No source-library
declarations or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing base-change factor lemma uses canonical full restrictions,
RelativeProductBaseChange.Product/Change and Witness, whereas the parent uses
arbitrary normalized RelativeProductPresentation and RelativeKunnethCube.
Applying that declaration directly does not prove the parent square: equality
transport, the Cartesian v-face, full-faithful normalization and the endpoint
identifications still have to be supplied. This work is recorded in the
cube-factor-transport node rather than silently assumed.

The closed formula uses the four concrete compact-section constructions, so a
point-fibre/model transport remains after evaluating the six-factor
isomorphism. Its independent source proof is recorded in the closed-fibre node.

Searched the existing source Kunneth/RelativeMap and Relative modules. They
supply finite etale coefficient results, not the supplied datum's four-stage
normalized cube and coefficient/proper assertions. Mathlib LeanSearch, Loogle,
LeanFinder and source grep queries are recorded in searches.jsonl and the new
nodes. Empty schemes, zero inputs, identity base changes, and every positive
finite exponent are retained; the impossible exponent zero has the original
hn contradiction. No statement is weakened.

## New nodes

- def-sf-relative-kunneth-constructions owns the unchanged constructions and
  comparisons previously in the theorem module. It adds no mathematical data.
- lem-sf-relative-kunneth-cube-factor-transport states the six individual
  transported base-change squares and endpoint identifications; source:
  coherence (iii) and the existing factor-square lemma.
- lem-sf-relative-kunneth-closed-fibre states the point-fibre specialization on
  ordinary closed restrictions; source: proof step (5) and final display.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
