## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.MonoidalChartDenseInjective`
with a complete Lean reduction, keeping both existing definitions and the theorem
signature verbatim. Added the proof-only import
`Sheaf.AlgebraicGeometry.FiniteChartTrivialityLocus` and a proof-only algebraic
closure import. All added helpers in the assigned module are private and proved.

The assigned module now proves directly:
- nonvanishing of each chart monomial by empty-ideal contraction;
- nonvanishing of finite products, including the empty product;
- injectivity of `(p,u) ↦ u*a(p)` by contraction of the two principal monoid ideals,
  cancellation, sharpness, and domain cancellation;
- the canonical chart-with-units bijection, using the structural injectivity for
  injectivity and the chart's surjectivity after transport of ring units;
- density, by constructing the marked field-valued lift to the actual affine
  colimit, taking the zero prime of its domain, and specializing to the marked
  prime over each point of an arbitrary nonempty open.

The single new theorem isolates the geometric chart argument of original steps
3, 4, and 6: the open triviality locus, its chart and strict-local principal-open
formulas, and restriction of log sections to units. It has no domain or monoid
ideal contraction hypothesis and asserts none of the parent's nonvanishing,
density, stalk product bijection, or structural injectivity conclusions.
Its docstring and node contain the complete proof in words, and the assigned
module supplies all algebraic and density arguments that combine it with the
original hypotheses. This is a decomposition with proved algebra and density,
not an axiom-free completion of the original theorem.

## Proved and sorry left

Closed the original syntactic hole in
`AlgebraicGeometry.FineSaturatedLogScheme.monoidalChart_dense_injective`
(node `lem-trf-monoidal-chart-dense-injective`): 1 of 1 original sorries replaced.
There are zero sorries in the assigned module.

Added one sorry, exactly the named public theorem
`AlgebraicGeometry.FineSaturatedLogScheme.finiteChart_trivialityLocus`
in `Sheaf.AlgebraicGeometry.FiniteChartTrivialityLocus`
(node `lem-trf-finite-chart-triviality-locus`). The delivery is a decomposition:
1 upper hole closed, 1 strictly smaller geometric hole added, net hole change 0.

Validation: both final files compiled cleanly through `lcompile.py`, without
errors or warnings. The geometric module compiled in 4.4 s and the assigned
module in 9.1 s. A direct textual comparison confirmed that the existing theorem
signature and both existing definition bodies are byte-identical to the source.
All Lean lines are at most 100 characters.

## No longer needed

Removed the assigned module's private import
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`. The openness argument now
belongs to the new geometric item, whose node still cites
`lem-weil-pbc-flat-lfp-open`. That node and Mathlib module are therefore not
pruned from the argument as a whole. The other original imports are public
statement imports and remain verbatim.

The main node no longer uses `def-weil-etale-morphism` or
`lem-weil-pbc-flat-lfp-open` directly in its proof; both are retained through the
new geometric node. No existing node or module is withdrawn or globally pruned.
The proof of the chart-with-units bijection does not use the chart pushout's
kernel congruence or the characteristic identification: after proving the
structural product injective, the chart's surjectivity and the canonical unit
comparison suffice. Existing hypotheses and definitions remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or required interface repair was found. The existing DAG
correctly describes the mathematics, but its geometric step 3 involves locality
of geometric ring germs, the chart pushout, and compatibility of the canonical
colimit comparison with all germs. Those are substantial formal glue, so the
geometric subargument is now a separate named theorem instead of a sorry inside
the main proof. The original statement, blueprint unit, and unit route are
unchanged. Read the current unit and ILO VI 1.1–1.4 (printed p. 69), and checked
the existing chart map, log units, strict henselization, and structural morphism
definitions and the universally-open Mathlib dependency.

Checked edge cases: the empty scheme, the trivial monoid and empty generating
list (products 1 and D(1)), repeated generators, the empty monoid ideal, and a
zero ring (excluded at an existing geometric point by the domain hypothesis).
The new geometric lemma needs neither domain nor contraction; its nonvanishing
open may be empty. Non-sharp chart monoids are excluded only in the parent's
algebraic injection argument. All private helpers have complete Lean proofs.

## New nodes

`lem-trf-finite-chart-triviality-locus`, in
`dag/nodes/sec-trace-formula/lem-trf-finite-chart-triviality-locus.json`, carries
only the geometric part of original steps 3, 4, and 6, with no density or
structural injectivity assertion. It inherits the original chapter, unit,
source, and blueprint ancestry. LeanFinder, LeanSearch, Loogle, Mathlib grep,
project rg, and blueprint searches found no existing statement. Recorded hits
concern ordinary free/smooth/etale loci, basic opens, and topological fibre
bundles, not log chart triviality. No change record is required: no existing
signature, definition, public import, or other item's node was changed.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
