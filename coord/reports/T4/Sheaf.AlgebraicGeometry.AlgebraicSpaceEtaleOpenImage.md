## What changed

Filled the four theorem bodies in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage`, preserving every public
signature and public import. The proofs assemble the existing DAG dependencies:

- The atlas criterion follows by comparing the final topology with the topology
  supplied by `exists_affine_etale_cover_and_point_topology`.
- The point-image map is an order embedding by `point_open_calculus`. The invariant
  open quotient makes it surjective, giving `OrderIso.ofSurjective`.
- The order isomorphism selects the open image. The existing open-factor and
  scheme-test theorems give the factorization, etaleness, surjectivity and arbitrary
  base-change equality. The factor point map is continuous through the open
  embedding, and surjective by equality of point images. Mathlib then gives
  compactness of the image.
- For the compact-atlas criterion, colimit uniqueness transports the canonical
  coproduct's disjoint affine open components to the supplied affine atlas. The
  existing finite-subatlas theorem selects a compact open restriction; its
  scheme-atlas compactness clause proves the reverse implication.

Added four private proof imports: `AlgebraicSpacePointOpenCalculus`,
`SpaceInvariantOpenQuotient`, `AlgebraicSpaceOpenFactorSchemeTests` and
`AlgebraicSpaceFiniteAffineSubatlas`. Three proved private helpers identify point
images with point-map ranges, prove composition of point maps, and show that a
sectionwise range subfunctor has the original map's point image. No new definition,
public declaration, axiom or split-off statement was added.

Updated the item's DAG proof, proof dependencies and proof origin to describe
these Lean arguments. Its statement and statement dependencies are unchanged.

Validation: the complete delivered module compiled cleanly through `lcompile.py`
in 6.1 seconds, with no warnings or errors and no `sorry` tokens.

## Proved and sorry left

Closed all four original holes:

- `AlgebraicGeometry.AlgebraicSpace.points_atlas_isOpen_iff`
- `AlgebraicGeometry.AlgebraicSpace.openSubspace_points_orderIso`
- `AlgebraicGeometry.AlgebraicSpace.etale_open_image`
- `AlgebraicGeometry.AlgebraicSpace.points_compactSpace_iff`

All four realize `lem-a1-space-etale-open-image`. Zero holes remain in the delivered
module; zero holes were added elsewhere; zero statements were split off. This is
an assembly from existing stated dependencies, several of which still have
`sorry` proofs. It does not assert that the transitive axiom closure is finished.

## No longer needed

Removed these private imports from this module:

- `Sheaf.AlgebraicGeometry.EtaleRelationQuotient`
- `Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`
- `Sheaf.AlgebraicGeometry.EtaleAtlasPresentation`

The first two geometric constructions and the atlas-presentation theorem belong
inside the existing invariant-open quotient dependency; the assembly does not use
them directly. The algebraic-space definitions are already supplied by the
unchanged public imports. The quasi-separatedness import supplies nothing used
by the proofs. These removals do not claim that these modules are globally unused.

Removed the item's direct proof dependency on
`lem-trf-space-fibre-products-etale-covers`: testing atlas etaleness against the
atlas itself directly supplies the representing square needed by the quotient
lemma. The unchanged statement dependency and public import remain, and other
lemmas still use fibre-product closure.

Removed the obsolete direct `tool_uses` entries
`lem-trf-space-fibre-products-etale-covers`,
`lem-trf-etale-relation-quotient` and
`lem-trf-etale-relation-finding-opens`; their needed mathematics remains in the
existing dependencies. No module was withdrawn. The unit route was preserved.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The module's old private imports and docstring
proofs predate the DAG's existing four-child split. The proof now uses those
children rather than redoing their geometry. The representing square obtained
from `IsEtale` has one presheaf-valued leg; Yoneda fullness supplies the second
scheme morphism required by `space_invariant_open_quotient`. The affine-cover and
finite-subatlas declarations use different coproduct presentations; the explicit
colimit isomorphism and transport of component opens bridge them without changing
either declaration. Empty spaces and empty coproducts require no extra hypotheses.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
