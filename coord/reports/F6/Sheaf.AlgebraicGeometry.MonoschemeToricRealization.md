## What changed

Filled five existing theorem proofs in
`Sheaf.AlgebraicGeometry.MonoschemeToricRealization` without changing statements,
definitions, attributes, or imports:

- `AlgebraicGeometry.Monoscheme.realizationι_over`: install the existing open-diagram
  and local-directedness witnesses and apply `CategoryTheory.Limits.colimit.ι_desc`.
- `AlgebraicGeometry.Monoscheme.realizationι_open`: use Mathlib's open-immersion
  instance for injections into a locally directed colimit of schemes, with exactly
  the witnesses used to construct the realization.
- `AlgebraicGeometry.Monoscheme.ToricComponent.generic`: apply the specification
  of the existing unique generic-point theorem to the supplied component chart.
- `AlgebraicGeometry.Monoscheme.componentChart_range`: each component chart's
  open image is below the defining supremum of component chart images; Mathlib's
  `Scheme.Opens.range_ι` identifies this open with the component inclusion's range.
- `AlgebraicGeometry.Monoscheme.componentChart_over`: compose the defining
  open-immersion lift with the component inclusion using
  `IsOpenImmersion.lift_fac`, then apply `realizationι_over`.

These are the arguments already described in the declaration docstrings, so no
DAG route change is needed. The definition node has no numbered proof plan and
no proof dependencies. Its existing statement dependencies remain needed by the
unchanged definitions and remaining obligations. Searches with leanfinder,
loogle, launcher grep and local rg located the Mathlib colimit and open-immersion
APIs; there is no duplicate monoscheme realization in the adopted source tree.
The full sandbox item compiled through `lcompile.py` without warnings or errors
in 8.5 seconds, below the 60-second limit.

## Proved and sorry left

Original holes: 12. Closed: 5. Added: 0. Remaining: 7. This is a partial proof
delivery, with no decomposition and no split-off statements.

Closed declarations (all in namespace `AlgebraicGeometry.Monoscheme`):
`realizationι_over`, `realizationι_open`, `ToricComponent.generic`,
`componentChart_range`, and `componentChart_over`.

The following existing named theorem holes remain unchanged. Each is attached to
`def-trf-monoscheme-toric-realization` and retains its source and proof in words:

- `AlgebraicGeometry.Monoscheme.sharpening_properties`
- `AlgebraicGeometry.Monoscheme.realizationDiagram_open`
- `AlgebraicGeometry.Monoscheme.realizationDiagram_locallyDirected`
- `AlgebraicGeometry.Monoscheme.existsUnique_componentGenericPoint`
- `AlgebraicGeometry.Monoscheme.existsUnique_torusAction`
- `AlgebraicGeometry.Monoscheme.existsUnique_realizationMap`
- `AlgebraicGeometry.Monoscheme.existsUnique_torusEmbedding`

The new proof of `realizationι_open` uses the existing open-diagram and
local-directedness theorem holes; `ToricComponent.generic` uses the existing
unique generic-point theorem hole. These are existing dependencies, not new
axioms or split-off obligations. No data construction was replaced by choice.

## No longer needed

None. No imports, nodes, modules, or declarations are removed. The existing
public imports supply the unchanged statements and constructions. No additional
proof imports are needed; the proofs use Mathlib APIs already available and
preceding declarations in the item itself. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical or tool defect was found in these five obligations. The item's
DAG node is a definition node with an empty proof list, rather than a theorem
with the numbered proof plan described by the generic brief. The existing
individual theorem docstrings supply the arguments followed here. The seven
remaining obligations require the additional monoid-chart, sharpening, or
gluing arguments described in their existing docstrings.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
