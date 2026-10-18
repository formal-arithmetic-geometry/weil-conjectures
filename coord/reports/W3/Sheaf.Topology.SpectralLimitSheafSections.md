## What changed

Proved `TopCat.Sheaf.spectralLimit_sheaf_sections` with its original signature unchanged.
The proof evaluates the sheaf colimit on the compact limit open, proves injectivity by
finite-stage detection of zero, and proves surjectivity by finite-stage generation.
It uses concrete filtered-colimit representatives rather than constructing a double colimit.

Added five fully proved auxiliary modules:

- `Sheaf.Topology.AbelianLargeCompactOpenColimit`: compact-open evaluation for
  `AddCommGrpCat.{max u v}` on spaces in `Type u`. This adapts the proved source module
  `WeilConjectures.Topology.AbelianSectionsFilteredColimit`, replacing its old stalk API
  with generic site point fibers. It also supplies the small filtered-colimit instance.
- `Sheaf.Topology.AbelianPullbackLocalSections`: local unit representatives, using
  uniqueness of left adjoints to the skyscraper functor, including the unit formula.
- `Sheaf.Topology.SpectralLimitDescendFiniteCover`: simultaneous descent of a finite
  compact-open covering and its prescribed inclusions, from the existing open-descent theorem.
- `Sheaf.Topology.SpectralLimitUnitZero`: a coefficient section with zero inverse-image
  unit vanishes at a later coefficient stage. This does not require a coefficient cocycle.
- `Sheaf.Topology.SpectralLimitUnitGeneration`: refine local representatives by compact
  opens, descend a finite covering, make differences zero on compact overlaps at one
  later stage, glue there, and identify the resulting unit by sheaf separation.

Updated the item's DAG proof and dependencies, and added nodes for all five auxiliaries.
No existing statement, definition, visibility or target changed. No consumer adaptation
or change record is required. The sole importing consumer remains
`Sheaf.Topology.SpectralLimitCohomology`.

Validation: all six sandbox modules compile together on the server without warnings.
The generation module compiled in 17.8 seconds and the item in 9.4 seconds in the final
proof pass. Empty opens, empty finite covers and overlaps, non-antisymmetric directed
preorders, and independent coefficient universes were checked in the statements and proof.
Finite upper bounds explicitly include a fixed index, so the empty-family case is valid.

## Proved and sorry left

Original holes: 1. Closed: 1. Added: 0. Remaining in the delivery: 0. This is a proof,
not a decomposition with new holes.

Closed `TopCat.Sheaf.spectralLimit_sheaf_sections`.
Also proved `TopCat.abelianCompactOpen_preservesDirectedColimits`,
`TopCat.Sheaf.abelianPullback_localSections`,
`Topology.spectralLimit_descend_finite_cover`,
`TopCat.Sheaf.spectralLimit_unit_eventually_zero`, and
`TopCat.Sheaf.spectralLimit_unit_generation`.
The additional filtered-colimit instance is proved as well. Every private helper is proved.
There is no `sorry` in any delivered Lean file.

These proofs use the already stated topology dependencies
`Topology.spectralSpace_directedLimit` and `Topology.spectralLimit_descend_opens`.
Their pre-existing holes are not changed or duplicated by this delivery.

## No longer needed

Removed these proof imports from the item:

- `Sheaf.Topology.SheavesDirectedColimitSections`;
- `Sheaf.Topology.SpectralLimitPullbackSections`;
- `Mathlib.Algebra.Colimit.Module`;
- `Mathlib.CategoryTheory.Limits.Types.Filtered`;
- `Mathlib.CategoryTheory.Sites.PreservesSheafification`.

The first two planned project lemmas are replaced by direct abelian proofs in the
required universes. The route does not use the chosen set-valued inverse-image
composition isomorphisms of `Sheaf.Topology.SetsInverseImageComposition`.

Removed the following old proof dependencies: `def-weil-directed-colimit-abelian-groups`,
`lem-weil-pbc-filtered-colimit-sets-elementwise`,
`lem-pc-sites-sheafification-underlying-sets`,
`def-weil-pbc-sheafification`, `def-weil-pbc-topological-inverse-image`,
`def-weil-spectral-space`, `lem-weil-pbc-sheaves-directed-colimit-sections`, and
`lem-weil-pbc-spectral-limit-pullback-sections`.
The topology, inverse-image and sheafification definitions remain available through
statement dependencies; this removal concerns their redundant proof-dependency edges.
The elementwise group/set and underlying-set sheafification nodes are unnecessary for
this argument: the proof uses Mathlib's concrete colimit API and generic site point fibers.
Withdrew the old `tool_uses` entry for `lem-pc-sites-sheafification-underlying-sets`.
Kept the spectral-limit and category-colimit dependencies that the proof actually uses.

## Where the brief, the DAG or earlier work was wrong

No statement was disputed and the unit route is unchanged. The available fixed-sheaf
spectral-limit theorem has `Type u` coefficients, whereas the assigned theorem has
`AddCommGrpCat.{max u v}` coefficients. The source library's proved abelian compact-open
colimit theorem also equates the space and coefficient universes. Neither specializes
by a direct application to the assigned statement. The new universe-explicit auxiliaries
supply the needed result without changing the assigned signature. Their statements
record this size distinction, rather than silently identifying the two universes.

## New nodes

`lem-weil-pbc-abelian-large-compact-open-colimit` states the independent-universe extension
of compact-open abelian colimit evaluation. Its complete Lean proof uses generic point
fibers and concrete filtered-colimit representatives. No hole remains.

`lem-weil-pbc-abelian-pullback-local-sections` states local unit representability for the
constructed abelian inverse image with the larger coefficient universe. Its fiber
isomorphism and formula on units are proved by adjunction. No hole remains.

`lem-weil-pbc-spectral-limit-descend-finite-cover` packages precisely the simultaneous
finite covering and inclusion descent used by generation. It is proved from parts
(1), (2), and (3) of the existing open-descent declaration. No hole remains.

`lem-weil-pbc-spectral-limit-unit-eventually-zero` detects a zero unit on any compact
stage open. Its proof uses skyscrapers, compactness and descent of an inclusion; it
needs neither a cocycle of coefficient maps nor the sheaf colimit. No hole remains.

`lem-weil-pbc-spectral-limit-unit-generation` is the finite-stage representation part
of the argument. Its full Lean proof combines local representatives, simultaneous
cover descent, zero detection on overlaps and sheaf gluing. No hole remains.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
