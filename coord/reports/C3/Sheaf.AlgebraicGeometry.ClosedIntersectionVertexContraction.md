## What changed

Replaced the whole proof hole of
`AlgebraicGeometry.ClosedIntersection.closed_intersection_vertex_contraction`
by a compiling assembly from the existing signed-refinement theorem and four
strictly smaller intermediate statements. The original theorem's signature,
public imports, and docstring are unchanged. No shared existing module or
definition was changed.

The item now proves the following glue directly, with private helpers:

- `row_support`: the cardinality bounds make the degree-index type empty outside
  -1,...,m-1. Projection extensionality makes its product functor zero; evaluation
  and the specified term isomorphism give the row's support.
- `closed_restriction_exact`: the ringed open-closed theorem gives exact closed
  direct image, and immersion inverse-image limit preservation gives exact
  inverse image. Their composite is exact.
- `affine_acyclic_detection`: proved for any open cover, using the existing
  Zariski-cover slice module detection, actual-ring open comparison, and
  preservation of homology by exact open inverse image. Affineness is unnecessary
  for this helper, but the original conclusion and its hypotheses stay intact.
- `disjoint_open_direct_image_zero`: a test object over a disjoint open has empty
  fibre product with the closed support; the empty covering forces its module
  sections to vanish. The open comparison and faithful module equivalence
  transport this to actual module inverse image.
- `row_zero_of_terms` and `row_vanish_off_support`: evaluation and exact open
  inverse image preserve the finite product of summands. The resulting limit of
  zero objects is zero, giving vanishing in every row degree.

The new geometry lemma supplies the intersection hypotheses and their base-change
stability. The augmented-row bridge consumes a `SignedClosedRow`, rather than
assuming any exactness or contraction. The open-comparison lemma supplies only
`OpenCompatibility`. The affine-vertex lemma supplies only the prescribed
`VertexContraction` for a given affine row. These are separate steps of the
original argument; none restates the original theorem or packages all its
conclusions as a hypothesis.

Validation: all five modules passed `lcompile.py --all` after final import cleanup.
The main module compiled in 14.9 seconds; the four intermediate modules took
7.4-8.3 seconds each. The original theorem signature was also compared verbatim
with the repository source and is identical. Edge cases checked in the
statements and proof descriptions: m=0 where no vertex is requested, m=1, empty
closed members, empty index, empty base and empty cover, degrees -1 and m-1, and
degrees outside the support. No covering assumption on the closed family was
introduced. No arbitrary object is defined by selecting an unproved existence
witness.

## Proved and sorry left

Original holes closed: 1, the body of
`AlgebraicGeometry.ClosedIntersection.closed_intersection_vertex_contraction`
(node `lem-sfb-closed-intersection-vertex-contraction`). Its assembly has no local
`sorry` and uses the four intermediate statements below.

Holes added: 4, each the entire proof of a public theorem in its own new module:

- `AlgebraicGeometry.ClosedIntersection.closed_intersection_geometry`
  (`lem-sfb-closed-intersection-geometry`).
- `AlgebraicGeometry.ClosedIntersection.row_from_signed`
  (`lem-sfb-closed-intersection-row-from-signed`).
- `AlgebraicGeometry.ClosedIntersection.closed_intersection_open_comparison`
  (`lem-sfb-closed-intersection-open-comparison`).
- `AlgebraicGeometry.ClosedIntersection.closed_intersection_affine_vertex`
  (`lem-sfb-closed-intersection-affine-vertex`).

The item module has zero remaining direct holes. The delivery has four direct
holes. This is a decomposition (1 closed, 4 added), not a net sorry reduction or
a claim that the full vertex theorem is now independent of sorry. The existing
`AlgebraicGeometry.closedRestriction_signed_refinements` is used as the declared
upstream dependency; its existing hole is not changed or counted as newly added.

## No longer needed

Removed the following private proof imports from the item:

- `Sheaf.AlgebraicGeometry.ProEtaleOrdinaryPullbackComparison`.
- `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafBaseChangeMates`.
- `Sheaf.CategoryTheory.FiniteTypeRestrictionExact`.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Mathlib.CategoryTheory.Adjunction.Mates`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.

The main proof uses the concrete immersion exactness and open-localization APIs
instead of invoking geometric inverse-image exactness and slice-exactness
presentations directly. The ordinary pullback comparisons and arbitrary-ring
base-change mates remain planned dependencies of the new comparison/contraction
nodes; their mathematics is not withdrawn. The geometric base-change facts move
to the geometry node. The signed-row theorem already encapsulates its
conjugate-unit argument. Shared declarations remain untouched.

Accordingly removed obsolete direct tool approvals from the parent, preserving
the order of those retained: `lem-pc-quasi-compact-base-change`,
`lem-sf-ring-sheaf-base-change-mates`, `lem-trf-geometric-inverse-image-exact`,
`lem-weil-pbc-closed-immersion-base-change`,
`lem-weil-pbc-conjugate-iso-unit-equation`,
`lem-weil-pbc-finite-type-restriction-exact`,
`lem-weil-pbc-module-sheaves-colimits-forgetful`, and
`lem-weil-proetale-weakly-etale-localization`. Some are still needed below the
new or existing dependency nodes; these removals are from the parent's direct
argument only. No whole module or node is claimed globally unnecessary, and no
module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false target or definition was found. The signed-refinement statement is
expressed with a degree-zero augmentation and ordered tuples, whereas this item
uses a single integer-indexed augmented complex and finite subsets. Applying it
alone does not produce the required `Row`; the bridge records this real missing
construction explicitly. The existing ringed open-comparison and Zariski-cover
module-detection results give a shorter formal locality argument than rebuilding
sheaf separatedness here. The original node's unit route is retained, and no
unit or chapter record is changed.

## New nodes

`lem-sfb-closed-intersection-geometry`, module
`Sheaf.AlgebraicGeometry.ClosedIntersectionGeometry`: step 1, finite-intersection
closedness, factorization, quasi-compact complements, and stability of the input
family under arbitrary base change. It contains no sheaf or homotopy assertion.

`lem-sfb-closed-intersection-row-from-signed`, module
`Sheaf.AlgebraicGeometry.ClosedIntersectionRowFromSigned`: step 2, insertion of the
support augmentation and reindexing ordered tuples by finite subsets. It assumes
only the existing signed-row data and asserts no exactness or comparisons.

`lem-sfb-closed-intersection-open-comparison`, module
`Sheaf.AlgebraicGeometry.ClosedIntersectionOpenComparison`: step 3, the full
unit-normalized open compatibility for a given row, without affine contraction.

`lem-sfb-closed-intersection-affine-vertex`, module
`Sheaf.AlgebraicGeometry.ClosedIntersectionAffineVertex`: steps 5-7, affine closed
base-change and the specified signed insertion contraction for a given row and
vertex. It asserts no existence of an original row, term exactness, locality, or
open compatibility.

Each node has its exact Lean statement, source, complete proof in words, logged
LeanSearch/LeanFinder/grep searches, and inherited chapter/unit and blueprint
provenance. The parent proof, proof dependencies, and proof origin match the
formal assembly. No change record is needed: no existing public signature,
definition, instance, attribute, or public import changes.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
