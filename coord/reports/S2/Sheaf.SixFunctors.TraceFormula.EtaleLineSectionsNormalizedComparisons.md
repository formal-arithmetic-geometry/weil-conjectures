## What changed

Replaced the sole hole in
`AlgebraicGeometry.Scheme.etale_line_sections_normalized_comparisons` by a coordinate
argument. The original statement and all public imports are unchanged.

`Sheaf.SixFunctors.TraceFormula.EtaleLineSectionsCoordinates` states the remaining
construction of the section functor, additive coordinates, normalized forward unit
and restriction comparisons. It asserts four coordinate formulas, without the
inverse-unit formula, beta naturality, identity/composition coherence, unit
compatibility, or frames for every prescribed cover.

`Sheaf.SixFunctors.TraceFormula.TensorSectionsCoordinateCoherence` proves the
identity, composition and structure-unit equations directly for tensor sections of
arbitrary scheme modules. Its private helpers specialize Mathlib's left-adjoint
unitality and associativity and the adjunction characterization of the structure map.
The assigned theorem uses these equations in its additive section coordinates.
Naturality of beta follows from naturality of the inverse composition comparison;
coordinate injectivity proves the identity and composition laws. Applying the
inverse tensor-unit map proves the inverse-unit formula. The final frames are
explicit composites of beta, the functor image of the supplied frame, and epsilon.
The cover proof uses the small-etale covering-sieve criterion directly.

Only the assigned module, three new modules and their DAG records are changed.
No shared interface is modified. The inherited unit route is retained.

The generic adjunction-coordinate argument is packaged as a proved theorem in
`Sheaf.SixFunctors.TraceFormula.SectionAdjunctionCoordinateCoherence`. Moving
cancellation to abstract left adjoints first reduced concrete elaboration cost,
but the combined coherence file still exceeded 60 seconds on a clean check.
This self-contained generic module exposes the resulting equations, so the tensor
module instantiates its theorem instead of reducing those proofs again.
The assigned module also treats tensor pullback locally as irreducible; this
prevents coherence applications from expanding its construction and changes no
exported attribute.

Validation after the repair: `lcompile.py --all` passes for all four modules against
current main. The construction, generic coherence, tensor coherence and assigned
modules report 3.7 seconds, cached 0.0 seconds, 25.0 seconds and 30.9 seconds
respectively. A project-import traversal finds no cycle and no dependency on
`SchemeEtaleInvertibleComparison` from the delivered modules. No profiler or raised
limit remains.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.etale_line_sections_normalized_comparisons`
(node `lem-trf-etale-line-sections-normalized-comparisons`).

Added one remaining hole:
`AlgebraicGeometry.Scheme.etale_line_sections_coordinates`
(node `lem-trf-etale-line-sections-coordinates`). Its source and complete proof
in words are in its docstring and node. This is the object and comparison
construction, strictly part of the original argument.

`AlgebraicGeometry.Scheme.trf_tensor_sections_coordinate_coherence`
(node `lem-trf-tensor-sections-coordinate-coherence`) is proved.
`AlgebraicGeometry.Scheme.section_adjunction_coordinate_coherence`
(node `lem-trf-section-adjunction-coordinate-coherence`) is also proved.

Thus the assigned module has zero holes. One original hole is closed and one
lower hole is added: this is a decomposition, with zero net holes closed.
There are no holes in definitions or private declarations.

## No longer needed

Removed these proof imports from the assigned module:

- `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`
- `WeilConjectures.AlgebraicGeometry.EtaleTensorUnitRestrictionEquation`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
- `Mathlib.CategoryTheory.Adjunction.CompositionIso`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites`

Their necessary construction and coherence work is represented by the new nodes;
these removals do not withdraw any source-library declaration or module. The
structure-sheaf import is used privately by the tensor coherence module. The generic
coherence module publicly imports adjunction composition because its statement uses
those comparisons. The remaining construction still needs quasi-coherent descent,
semilinear restrictions, adjunctions and the Zariski-to-etale local-frame argument.
The original item's direct proof dependencies and its obsolete direct tool-use
approvals are replaced by the new construction and coherence nodes.
The removed direct approvals are
`lem-sc-etale-qcoherent-presheaf-functorial`, `lem-sc-etale-qcoherent-descent`,
`lem-pc-module-pullback-adjunction`,
`lem-weil-pbc-module-pullback-structure-sheaf`,
`lem-sc-etale-tensor-unit-restriction-equation`,
`lem-weil-pbc-module-pullback-quasi-coherent`,
`lem-sc-left-adjoint-composition-iso-associativity`,
`lem-weil-pbc-conjugate-iso-unit-equation`, and
`lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`. Except for the
quasi-coherence-of-pullback lemma discussed below, they remain dependencies of
the split construction or proved coherence lemmas.

The separate quasi-coherence-of-pullback dependency
`lem-weil-pbc-module-pullback-quasi-coherent` is unnecessary here: pullback
invertibility follows by comparison with ordinary module pullback and its
`Modules.IsInvertible.pullback` instance; invertibility already supplies
quasi-coherence when applying tensor-section descent. The standalone
Zariski-to-etale morphism-of-sites theorem is unnecessary for the final prescribed
cover clause, which follows from Mathlib's small-etale covering-sieve criterion.
It remains in the construction node for its general local trivialization argument.
No whole module is claimed pruned from the targets' import closure, and none is
withdrawn.

## Where the brief, the DAG or earlier work was wrong

Repaired the return of head `4a9fcbf7e7e`: main landing `3eceb7984f9` extracted
shared definitions into `SchemeEtaleLineDefinitions` and made the parent comparison
import this item. The retained proof and its two new specialized modules still
imported the parent comparison, creating a cycle. The assigned file is rebased on
current main, retaining main’s definitions import and the delivery’s proof. Both
`EtaleLineSectionsCoordinates` and `TensorSectionsCoordinateCoherence` now publicly
import `SchemeEtaleLineDefinitions` as requested. They use no parent comparison
theorem or R2 helper. The generic module is unchanged. The existing DAG node is
rebased on current main with only the delivery-owned proof fields reapplied.

No mathematical error was found. The apparent shorter route through
`scheme_etale_invertible_comparison` is unavailable: its DAG proof depends on this
item. The source and comparison signatures were retained. Checked the formulas
for the structure module, identity maps, arbitrary module morphisms including zero,
and arbitrary covers; neither an inhabited index type nor a nonempty scheme is used.

## New nodes

`lem-trf-etale-line-sections-coordinates` is the construction part of original
steps 1–4 and the local line-property part of step 8. It has its own Lean module
and the sole remaining named theorem hole. The main theorem supplies the other
six clauses from its coordinate formulas, so this is not a renaming of the item.

`lem-trf-tensor-sections-coordinate-coherence` records the proved tensor-coordinate
identity, composition and unit equations from original steps 5–7. These are stated
for arbitrary module sheaves, independently of a choice of the functor A or its
coordinates. No change record is needed: existing signatures, definitions and
public imports are unchanged.

`lem-trf-section-adjunction-coordinate-coherence` packages the proved generic
unit-section, inverse right-unit, and inverse associativity equations for any
family of left adjoints to scheme module pushforwards. It isolates the expensive
normalization calculation behind a theorem, without introducing any new data
choice or proof hole.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
