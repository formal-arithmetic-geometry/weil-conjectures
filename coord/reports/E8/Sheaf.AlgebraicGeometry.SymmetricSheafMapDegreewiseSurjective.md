## What changed

Proved `AlgebraicGeometry.SymmetricAlgebraSheaf.exists_map_degreewise_locallySurjective`
with its original signature. All added helpers are private and completely proved, in the
item module. No shared definitions or other existing modules were changed.

The proof constructs the algebra-sheaf map using the canonical universal property
`exists_quasiCoherentSymmetricAlgebra_core`. Its scalar equation is `Under.w`.
Sectionwise symmetric algebra maps commute with restrictions and the canonical section
maps. Induction on powers of the degree-one range proves preservation of degree and
pointwise local lifting: scalars lift directly; sums and products use intersections of
two neighborhoods. The homogeneous section definition supplies an affine representative
at each point, and the point-indexed family of lifting neighborhoods supplies the cover.
This treats degree zero and the empty open without an additional hypothesis.

Validation: the final imports compiled without errors or warnings in 15.3 seconds.
`#print axioms` for the target reported exactly `propext`, `Classical.choice`, and
`Quot.sound`; the temporary diagnostic command was removed before delivery.

Updated the item's proof, proof dependencies and proof origin to match this argument.
The canonical core universal property is used as a generic tool from `sk-thm-p1`; it is
already fully proved in Lean and replaces the larger existential quasi-coherent theorem.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.SymmetricAlgebraSheaf.exists_map_degreewise_locallySurjective`
(node `lem-trf-symmetric-sheaf-map-degreewise-surjective`). One of one holes closed;
zero holes added or split off; zero holes remain in the delivery.

## No longer needed

The full theorem `lem-weil-pbc-quasi-coherent-symmetric-algebra` and the pure-product
spanning theorem `lem-weil-pbc-symmetric-algebra-graded` are unnecessary as direct proof
inputs. The homogeneous-section definition already supplies the affine representative,
and submodule-power induction operates directly on the grade's definition. The proof
therefore needs no separate affine bijectivity theorem and no explicit finite monomial
presentation. The obsolete tool approval for the larger universal-property theorem was
removed from the item's `tool_uses` list.

Removed redundant direct imports of
`Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`,
`Sheaf.CategoryTheory.RingedSiteModules`, and
`WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`.
The first and third modules remain transitive statement dependencies through
`SymmetricHomogeneousSections`; no global module withdrawal is claimed.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid. Its explicit finite-sum presentation and
special treatment of degree zero can be replaced by submodule-power induction. The
existing target statement and definitions were kept unchanged. No new nodes were needed.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
