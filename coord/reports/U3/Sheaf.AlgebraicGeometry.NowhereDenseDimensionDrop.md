## What changed

Proved `AlgebraicGeometry.Scheme.topologicalKrullDim_lt_of_isNowhereDense` in
`Sheaf.AlgebraicGeometry.NowhereDenseDimensionDrop`, preserving its signature and visibility.
The shorter route chooses a Noetherian affine neighbourhood of each point of the closed subset,
then the generic point of an irreducible component through that point. If that generic point lay
in the closed subset, the component would lie there. Stacks Tag 0052 (3), as formalized by
`NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent`, would supply a nonempty
ambient open inside the subset, contradicting nowhere density. Thus every point generalizes
outside the subset. The already proved source-library theorem
`topologicalKrullDim_lt_of_forall_exists_specializes` supplies the chain-extension dimension bound.

Replaced the proof import of the global local-finiteness module with the proof-only import
`WeilConjectures.Mathlib.Topology.KrullDimension`. Updated the theorem's proof docstring and the
node's `proof`, `proof_deps`, and `proof_origin` to follow this affine-local argument. No statement,
definition, public import, consumer, or target changed; no change record is required.

Validation: the module compiles without warnings through `lcompile.py` in 3.1 seconds.
`#print axioms AlgebraicGeometry.Scheme.topologicalKrullDim_lt_of_isNowhereDense` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. The proof uses no unproved dependency. The import
cycle check permits the source-library topology import. All Lean lines have at most 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.topologicalKrullDim_lt_of_isNowhereDense`
(node `lem-sc-hilbert-nowhere-dense-dimension-drop`).

Added 0 holes; split off 0 statements. There are no remaining `sorry` declarations in this delivery.
The result covers the empty closed subset and dimension zero through the same chain-extension
argument. It does not require global quasi-compactness or a globally Noetherian scheme.

## No longer needed

Removed the import `Sheaf.AlgebraicGeometry.LocallyNoetherianComponentsLocallyFinite` and the proof
dependency `lem-sc-locnoeth-components-locally-finite`. Its declaration
`AlgebraicGeometry.exists_open_finite_irreducibleComponents` is not used by this proof.
The component-restriction/injectivity node `lem-sc-components-open-injection`, used by the old
local-finiteness route, is likewise unnecessary for this item. The affine Noetherian-space and
component-cover facts are retained, while the nonempty-open component fact is supplied directly
by the existing Mathlib leaf `lem-sfb-noetherian-component-open`. No module is withdrawn, and no
unit statement or realized proof step is bypassed (`sk-def-av-ample-degree.realized` is empty).

## Where the brief, the DAG or earlier work was wrong

The original argument is mathematically valid, but global local finiteness and a supremum over
components are unnecessary. Working in one Noetherian affine neighbourhood of each point yields
the exact generalization condition of a proved source-library theorem. This removes the only
holed proof dependency imported by the original module. No false statement or interface fault
was found. The Noetherian-space proof is passed explicitly at the component-open application to
avoid elaborator ambiguity between an open subscheme and its underlying subspace.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
