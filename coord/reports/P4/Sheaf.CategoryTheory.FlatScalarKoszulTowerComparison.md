## What changed

The original theorem is reduced to the genuinely separate finite strict Koszul
calculation `CategoryTheory.FlatScalarKoszul.strictScalarKoszulComparison`.
The theorem's statement, hypotheses, universes and coordinate maps are preserved.
The reduction obtains presentations and their normalized units from the existing
proved single-site Cech/Koszul comparison, descends the
strict comparison, and proves the normalized inverse-limit comparison, unit
square, every projection square, and empty-list identity.

The strict coordinates and restriction constructions now live in the new
`Sheaf.CategoryTheory.FlatScalarKoszulModels`, publicly re-exported by the item.
This avoids a cycle between the strict finite lemma and its derived application.
`limitComparison` has an explicit, definitionally equal endpoint type; its body
is unchanged. The change record is
`coord/changes/P4-flat-scalar-koszul-models.md`.

The retained finite lemma is independent of derived categories, flatness,
K-injective resolutions and inverse limits. Its source is Stacks 0A0E/0913.
The existing stated dependencies do not provide this coordinate-normalized
strict finite calculation. Ordinary module base-change isomorphisms do not
by themselves supply the sheaf Hom-dual model, ordered coordinates, tower
transitions and strict coaugmentation equation required here.

## Proved and sorry left

Closed in the item:
`CategoryTheory.FlatScalarKoszul.flatScalarKoszulTowerComparison`
(lem-weil-pbc-flat-scalar-koszul-tower-comparison), by reduction.

Added and retained:
`CategoryTheory.FlatScalarKoszul.strictScalarKoszulComparison`
(lem-weil-pbc-strict-scalar-koszul-comparison), one public theorem with its entire
proof postponed. Its docstring supplies the finite decomposition, differential,
transition, naturality and coaugmentation argument, including the empty list.

The item has zero textual holes; the delivery adds one hole in the finite lemma.
This is a decomposition of one hole into one strictly smaller hole, net zero,
not a claim that the entire comparison is axiom-free. No definition has a hole.
The supporting model module has zero holes.

## No longer needed

The proof does not use the general flat ringed-diagram restriction theorem
`lem-weil-pbc-flat-ringed-diagram-restriction`, module
`Sheaf.CategoryTheory.FlatRingedDiagramRestriction`: the existing Mathlib scalar
restriction and its tensor adjunction, whiskered by the tower shape, suffice.

The direct proof imports of
`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat` and
`Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated` are unnecessary.
The existing proved single-site Cech/Koszul comparison already supplies the
needed presentations and their units. Their general nodes
`lem-pc-bounded-above-flat-kflat-site` and
`lem-weil-pbc-kflat-fixed-tensor-triangulated` are not direct dependencies of this
proof; they remain needed by the specialized results elsewhere. The obsolete
direct tool-use entry for the bounded-above-flat theorem is removed.

The direct auxiliary imports
`Sheaf.CategoryTheory.RingedCechKoszulDualKFlat` and
`Sheaf.CategoryTheory.RingedCechKoszulHomLimitComparison` are also unnecessary.
Their nodes are not direct proof dependencies: the proved single-site comparison
already packages the required construction and its unit equation.

The general tower-category levelwise-abelian theorem
`lem-weil-tower-category-levelwise-abelian` is not used directly. The empty-list
argument instead uses the existing prescribed-presentation Cech/Hom comparison
and the invertibility of the evaluation-at-one unit. No declaration or module
of the adopted source library is withdrawn. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG described the finite strict calculation as elementary but
provided no Lean lemma for its ordered-coordinate decomposition. It is a
separate argument from derived inverse limit and is now recorded as such.
The original empty-list argument can be replaced by the already stated
prescribed-presentation comparison without constructing another constant-tower
K-injective model.

Some intermediate rewrites unfolded total-tensor and chosen-limit constructions.
Local irreducibility and explicit endpoint normalization keep these operations
abstract. The supporting definitions are moved for dependency direction, not to
split a slow proof across files. The original constructions and target meanings
are preserved. There are no forced adaptations of other groups' modules; the
item has no current Lean importers, and its unfinished DAG parents remain intact.

## New nodes

`def-weil-pbc-flat-scalar-koszul-models` attaches the existing, unchanged strict
coordinate and restriction definitions to their new supporting module. It adds
no mathematical object or proof hole.

`lem-weil-pbc-strict-scalar-koszul-comparison` is the finite ordered-coordinate
strict comparison of the original proof's first two steps, independent of
flatness and all derived constructions. Its exact Lean statement and complete
proof plan are recorded in its module and node. This is the one retained hole.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
