## What changed

Proved `AlgebraicGeometry.nagataRelativeGluingDatum_descends` in
`Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescends`, with its signature unchanged.
The chart clause transports the canonical pullback square through the fixed chart comparison.
The open clause uses `nagataQCOpenDescent_spec` and cone naturality twice. The morphism clause
uses `nagataMorphismDescends` in both directions, then proves compatibility of each raw
transport by its first and second pullback projections. All five private helpers are proved.
Updated the theorem's proof description and its node's proof, proof dependencies and origin.

The complete proof compiles through `lcompile.py` without errors or warnings. No definition,
public import, target statement or consumer module changes.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.nagataRelativeGluingDatum_descends`
(node `lemma-nagata-relative-gluing-datum-descends`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered Lean module.
The proof uses the existing stated theorems `AlgebraicGeometry.nagataQCOpenDescent_spec` and
`AlgebraicGeometry.nagataMorphismDescends`, whose separate obligations remain with their nodes.

## No longer needed

Removed direct imports:

- `Sheaf.Order.DirectedFiniteUpperBound`
- `Sheaf.AlgebraicGeometry.NagataAffineFpDescends`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Limits`

The Mathlib pullback API remains available through the retained public interface and
base-change module. The direct proof dependencies no longer include:

- `lemma-nagata-directed-finite-upper-bound`: the stage inequalities are retained fields.
- `lemma-nagata-affine-fp-descends` and `lem-weil-pbc-fibre-product-affine-spectra`: the chart
  comparison and its structure-map equation are retained fields, so no construction of a
  new chart comparison is needed.
- `lem-weil-pbc-affine-morphism-permanence`, `lem-weil-pbc-qcqs-morphism-permanence`,
  `lem-weil-pbc-quasi-compact-morphism-preimage-qc-open`, and
  `lem-nagata-qc-open-basechanged-affine-chart-fp`: the required qcqs and finite-presentation
  instances are retained in each two-way morphism choice.

Removed the obsolete top-level `tool_uses` entries
`lem-weil-pbc-fibre-product-affine-spectra`, `lem-weil-pbc-affine-morphism-permanence`,
`lem-weil-pbc-qcqs-morphism-permanence`, and
`lem-weil-pbc-quasi-compact-morphism-preimage-qc-open`; retained `def-pc-fibre-product`.
These are removals from this proof's dependency route, not claims that all their modules
leave the targets' entire import closure: the retained definitions and property theorems
can still use them transitively. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG plan reconstructs chart comparisons and derives finite-presentation hypotheses
that the current `NagataRelativeGluingDatum` already retains. Reusing those fields gives a
shorter proof with the same statement and follows the same chart/open/morphism route of
Stacks Tag 01ZM, `limits.tex`, `lemma-descend-finite-presentation`, proof of (1), i_2--i_4.
The unit's realized list is empty; its chart/open/morphism descent route is preserved.
No new mathematical assertion or definition repair was necessary.

The DAG records a Lean attachment for
`Sheaf.AlgebraicGeometry.NagataQCOpenBasechangedAffineChartFP`, but its recorded file is
absent from this shared checkout. This proof does not require it, so the stale attachment
is reported without changing that other node.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
