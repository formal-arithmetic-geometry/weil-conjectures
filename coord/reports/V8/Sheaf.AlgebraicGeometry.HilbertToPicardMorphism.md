## What changed

Proved `AlgebraicGeometry.exists_hilbertToPicardMorphism` in
`Sheaf.AlgebraicGeometry.HilbertToPicardMorphism`, with its signature unchanged.
The universal Hilbert element gives the relative Cartier pair. The existing
`abelClass`, `abelClassIso`, and `abelClass_mem` API supplies its dual ideal class,
representative isomorphism, and degree. The inverse Picard representing equivalence
constructs gamma from the sheafification image. For every field-valued point,
`homEquiv_comp`, `pic_map_abelClass`, subtype extensionality, and sheafification
naturality prove the required compatibility.

Removed all twelve private proof imports; the unchanged public imports already
provide the APIs used. Updated the item's seven proof steps and proof dependencies
to describe this implementation; the universal-divisor route of the unit is kept.
No definitions, signatures, public imports, source-library modules, or consumers changed.

Validation: server single-file compilation of the complete proof passed. The final
pruned file is compiled again by the delivery checks, including its axiom probe.
The argument works uniformly for d = 0 and for an empty representing base: no
positive-degree or nonempty-base assumption is introduced. Both representative
isomorphisms are `abelClassIso` for the actual Hilbert elements.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.exists_hilbertToPicardMorphism`
(node `lem-sc-hilb-to-pic-morphism`). Added 0 holes. There are no sorries left in
the delivered module and no new modules or split-off statements.
The proof uses existing library theorems, whose transitive dependencies remain as
in the library; this is a proof of the assigned theorem, not an axiom-closure claim
for all imported modules.

## No longer needed

Removed private imports:

- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`
- `Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne`
- `WeilConjectures.AlgebraicGeometry.DimensionBaseChange`
- `WeilConjectures.AlgebraicGeometry.TensorPullback`
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`
- `WeilConjectures.AlgebraicGeometry.EffectiveCartier`
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`
- `WeilConjectures.AlgebraicGeometry.Picard.Defs`
- `WeilConjectures.AlgebraicGeometry.Picard.Degree`
- `WeilConjectures.AlgebraicGeometry.PicardFunctor`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`

The separate node `lem-sc-curve-base-change-relative-dimension-one` is not needed
by this implementation: `IsSmoothProjectiveCurve.smoothOfRelativeDimension` and
base-change stability already provide the instance used by the Hilbert/Abel API.
The node `lem-pc-dim-base-change` is also not needed: `abelClass_mem` computes the
fibre degree directly using the smooth relative curve and Hilbert rank. Both edges
were removed from this item's proof dependencies and step uses. Their modules are
not withdrawn: other parents may still need them.

The other removed imports are redundant direct edges to modules available through
the retained public imports, or proof-planning imports whose declarations are not
called here. The mathematical Cartier, line-bundle, degree, pullback, and Yoneda
dependencies remain in the node, including those used by the existing Abel lemmas.
No library module or declaration is deleted or claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The old proof plan did not mention the existing `abelClass` API in
`WeilConjectures.AlgebraicGeometry.Picard.Jacobian`; it already proves the geometric
and degree computations needed here. No new intermediate theorem is necessary.
The latest blueprint has reorganized the old `sk-prop-jacobian` material under
`sk-thm-picard-main`; the current proof still follows Stacks pic.tex,
`lemma-picard-pieces` (Tag 0BA0), clause (4), and
`remark-universal-object-hilb-d` (Tag 0B9J), retaining the universal divisor.
The repository's current return and rework records contain no entry for this item.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
