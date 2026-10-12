## What changed

Proved the original `AlgebraicGeometry.exists_flat_stage_of_limit` by a finite
geometric reduction, the existing `RingHom.exists_eventually_flat_of_colimit_flat`,
and the directed finite-upper-bound argument. Its signature and docstring are
byte for byte unchanged.

Added and proved `AlgebraicGeometry.exists_finite_affine_flat_models` in
`Sheaf.AlgebraicGeometry.FiniteAffineFlatModels`. The second reading closed its
initially proposed sorry using the already proved affine-open ring-system and
affine-chart tensor-comparison theorems, Mathlib finite subcovers, cancellation of
target open immersions, arrow-isomorphism invariance, and flatness locality.
No definitions or existing declaration statements changed.

Removed the unused public import `Sheaf.AlgebraicGeometry.LimitAffineTransition`
from the item and its ordinary import from the new helper. The helper instead has
ordinary proof imports of `Sheaf.AlgebraicGeometry.AffineOpenDirectedRingSystem`
and `Sheaf.AlgebraicGeometry.AffineChartTensorComparison`. The new helper import
in the item and the algebraic descent import are ordinary proof imports.
Import-interface change record: `coord/changes/descend-flat-prune-limit-import.md`.
The record lists all downstream modules. The sole direct importer,
`Sheaf.AlgebraicGeometry.DescendFiniteLocallyFree`, is checked against the overlay.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.exists_flat_stage_of_limit`
(node `lem-weil-pbc-descend-flat-finite-presentation`): 1 of 1 original holes closed.
The added theorem `AlgebraicGeometry.exists_finite_affine_flat_models`
(node `lem-weil-pbc-finite-affine-flat-models`) is also proved; its first-worker hole
was closed during the second reading and is not delivered. Holes added: none.
Both delivered modules contain no sorry.

The original imported theorem `RingHom.exists_eventually_flat_of_colimit_flat`
remains sorry in the repository. The main theorem therefore has `sorryAx` from
that existing dependency; the new geometric theorem uses only `propext`,
`Classical.choice`, `Quot.sound`. This is a net removal of one original hole,
not a claim that the transitive proof of flatness descent is finished.

Edge cases checked: an empty source/empty finite subcover, zero coordinate rings,
a singleton index, and a directed preorder without antisymmetry. The chosen i₀
ensures the tail is inhabited; directedness is proved. Compactness is only used
on X₀. No data is defined by choosing an arbitrary witness from an unproved
existence theorem; all existential elimination is inside theorem proofs.

## No longer needed

Removed item import: `Sheaf.AlgebraicGeometry.LimitAffineTransition`.
Removed new-helper proof import: the same module, replaced by the two proved
comparison modules. No globally pruned module is claimed: other target branches
may still import it.

The following original direct proof dependencies are no longer used directly by
the item's new proof (the affine geometry is provided by the proved helper and
its existing comparison dependencies):

- `lem-weil-pbc-affine-open-spec-points`
- `def-weil-pbc-scheme-conventions`
- `lem-weil-pbc-morphism-into-affine-scheme`
- `lem-weil-pbc-lfp-affine-opens-finite-presentation`
- `pqf-def-affine-morphism`
- `def-weil-pbc-category-colimit`
- `lem-weil-pbc-limit-affine-transition`
- `lem-weil-pbc-spec-colimit-limit`
- `def-pc-fibre-product`
- `lem-weil-pbc-open-fibre-product`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `def-weil-flat-morphism`
- `def-pc-scheme`
- `lem-weil-pbc-flat-ring-map-iff-flat-affine`
- `def-weil-pbc-flat-ring-map`

The only original direct proof dependency retained in the item is
`lem-weil-pbc-colimit-flat-ring-map`; the new direct dependency is
`lem-weil-pbc-finite-affine-flat-models`. The helper's direct proof dependencies
are `lem-weil-pbc-affine-open-directed-ring-system`,
`lem-weil-pbc-affine-chart-tensor-comparison`, and
`lem-weil-pbc-flat-ring-map-iff-flat-affine`. This is direct-dependency pruning,
not a claim that all these old nodes leave the target import closure.
The unit `sk-thm-p1` and every entry of its `realized` route remain untouched.

## Where the brief, the DAG or earlier work was wrong

The first worker missed existing proved `exists_affineOpen_directedRingSystem`
and `exists_affineChart_tensorComparison`; the proposed geometric hole can be
closed from them. The second reading used searches with different vocabulary:
LeanFinder found Mathlib flatness locality, and repository searches found the
compatible chart models. The second Loogle query reported an unknown identifier,
so its zero hits were not treated as evidence of absence. The new finite-family
packaging does not restate eventual flatness and is now fully proved.

The first-worker restoration of an unused public import avoided a change record
but left an unnecessary dependency. The second reading removed it with the
required record and checked the direct downstream importer. No mathematical
statement error was found. The earlier local source reading and source citation
remain applicable: Stacks Tag 04AI's affine reduction and Tag 01YW.

## New nodes

`lem-weil-pbc-finite-affine-flat-models`, module
`Sheaf.AlgebraicGeometry.FiniteAffineFlatModels`: a proved finite-family packaging
of existing compatible affine-chart models and flatness locality. It assumes no
limit flatness and concludes no eventual stage flatness. The ring maps at stages
and the limit use the canonical transition maps and colimit coprojections.
Its node records the actual proof, source, search history, creation, blueprint,
unit/chapter and exact Lean statement. No new sorry remains.

## Second reading by P2

1. Compared both delivered modules with the repository: the existing theorem's
   signature and docstring are byte for byte unchanged; the only existing interface
   change is the removed unused public import, covered by the change record.
2. Compiled both modules locally through lcompile.py, with no warnings or errors.
   Searched for sorry and forbidden declarations: none in either module. Scratch
   #print axioms checks found only the three permitted axioms for the new helper;
   the item additionally has sorryAx from the pre-existing algebraic descent hole.
   No hollow definition or unproved arbitrary-witness data construction occurs.
3. Checked the new theorem's mathematical construction, empty-source/zero-ring
   cases, and preorder tail. It is true and exactly supplies finite models and
   flatness equivalences. Different-vocabulary searches found existing ingredients,
   used to close the helper. It is a genuine geometric part of the argument, not
   the original descent assertion under another name. No split-off hole remains.
4. Read the proof from the original hole downward. The algebraic descent and finite
   upper-bound steps are kept; the helper now uses proved library comparisons and
   Mathlib locality. Imports and direct DAG dependencies are pruned and listed
   above. Inspected dag/units/sk-thm-p1.json: its realized route is unchanged.
5. Checked the original node diff and new node against the Lean. Updated the new
   node's proof, proof_deps and proof_origin to the actual closed proof; its Lean
   statement matches verbatim. The original node still matches the main proof.

Second reading changed: proved the geometric comparison; replaced its unused
limit import with existing comparison imports; removed the item's unused public
limit import with a change record; corrected pruning and hole counts in the report
and updated the new node's actual proof dependencies.
