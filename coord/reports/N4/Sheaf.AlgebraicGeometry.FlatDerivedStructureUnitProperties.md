## What changed

Proved `AlgebraicGeometry.flat_derived_structure_unit_properties` in
`Sheaf.AlgebraicGeometry.FlatDerivedStructureUnitProperties` from the existing canonical
base-change, single-pullback and degree-zero unit results, plus the new generic compatibility
lemma in `Sheaf.AlgebraicGeometry.CanonicalStructureMapBaseChange`.
The second reader adds its proof-only import of `ModuleBaseChangeMapAlgebra`,
which also makes the planned tensor structure-map dependency available.

The negative-cohomology branch uses `isIso_derivedBaseChange_of_flat_invertible`, the canonical
single pullback comparison and Mathlib's adjoint structure-module isomorphism. It transports
`isGE_rightDerivedFunctor_obj_singleFunctor` through the resulting fibre isomorphism.
The degree-zero branch proves the ordinary structure-module map invertible over a field:
there are only the empty and whole opens; the empty section rings are subsingleton, and the
whole-open map is `appTop`. `canonicalDirectImageH0Unit` gives invertibility of the other
factor. Applying homology to the compatibility identity and cancelling isomorphisms finishes
this branch. The proved field calculation is a private helper.

Added proof imports of `Picard.FlatInvertibleCanonicalDerivedBaseChange`,
`CanonicalStructureMapBaseChange`. The redundant direct proof import of the source
`LocallyFree` module was removed: the canonical single-pullback module already publicly
imports it. All original public
imports, signatures and visibility are preserved. Updated the item's node proof and proof
dependencies to this route. Both sandbox modules compile without warnings through `lcompile.py`. The new node now
records its Lean statement verbatim, including line breaks. The original theorem signature
and every original public import are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.flat_derived_structure_unit_properties`
(node `flat-derived-structure-unit-properties`). No sorry remains in the item's module.
The private helper `isIso_structureMap_over_field` is fully proved.

Added one hole:
`AlgebraicGeometry.canonical_structure_map_base_change`
(node `lem-sc-canonical-structure-map-base-change`), in the new module
`Sheaf.AlgebraicGeometry.CanonicalStructureMapBaseChange`. Its proof is exactly `by sorry`.
This is a decomposition (one hole closed, one hole added, net zero), not a complete axiom-free
proof of all dependencies. The new theorem is only the map identity for an arbitrary
commutative square: it asserts neither base-change invertibility nor either cohomology
conclusion. The other ingredients are existing library declarations; their own proof dependencies
remain outside this delivery. Its docstring and node give
the complete argument through the pinned derived-unit compatibility and ordinary adjunction
triangles.

The edge cases were checked in the statements and proof: no nonempty fibre is assumed;
the right-derived nonnegative statement applies also to the zero structure module. On the
empty open the field calculation explicitly uses terminality of sheaf sections. An empty
fibre cannot satisfy the `appTop` isomorphism hypothesis because a field is nonzero. The
new compatibility equation uses only functoriality and adjunction identities, so empty
schemes require no exception.

## No longer needed

Removed direct proof imports:

- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`: redundant new
  import from the earlier sandbox attempt, already publicly imported by the canonical
  single-pullback comparison module. Its module remains transitively imported.

- `Sheaf.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange`: replaced by its existing
  proved flat-invertible consequence; its node remains needed through that consequence.
- `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`: the comparisons in this proof use
  Mathlib's ordinary `pullbackObjUnitToUnit` isomorphism directly.
- `Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility`: needed by the new generic
  compatibility item rather than used directly in the main theorem.
- `Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose`: likewise moved to the
  new compatibility item's proof plan.

No module is removed from the transitive import closure of this item: a comparison of the
source import graphs before and after the delivery confirms this. Thus there is no claim
of a globally pruned module. The main node no longer directly needs
`lem-pc-relatively-flat-canonical-module-base-change`,
`lem-weil-pbc-module-pullback-structure-sheaf`,
`lem-pc-derived-base-change-unit-compatibility`, or
`lem-pc-canonical-single-adjunction-transpose`; their relevant uses are encapsulated in the
existing flat-invertible theorem or in the new compatibility node.

## Where the brief, the DAG or earlier work was wrong

The second reader found that the new compatibility module did not import its planned
tensor structure-map dependency. Added a plain import of `ModuleBaseChangeMapAlgebra`,
whose last clause already proves the ordinary structure-map identity needed in the
compatibility argument, and cited its node in that proof plan. This adds no module
to the item's transitive import closure.

No mathematical statement was changed or disputed. The DAG's route works, with the existing
flat-invertible derived base-change consequence avoiding a separate existential choice of
ordinary-target comparison. The missing glue is an equality of canonical maps, isolated in
the new node; it is not an arbitrary-map assertion.

`blueprint_refs.py ancestor flat-derived-structure-unit-properties` prints `None` because
its created-item chain names a Lean module. The new node inherits the existing item's
recorded ancestor `lem-sc-flat-derived-structure-unit` and prepends the item node to its
existing `via` list. The unit's own `realized` statement and proof steps are not bypassed.

LeanSearch returned an internal-server error and Loogle was unavailable. These failures
are recorded as unavailable; LeanFinder, launcher grep, local source searches and blueprint
searches were actually run. Stacks Tags 08HY and 0096 were read on their official pages.

## New nodes

`lem-sc-canonical-structure-map-base-change` states the generic compatibility of the explicit
canonical structure maps with pinned derived exchange, in
`lean/Sheaf/AlgebraicGeometry/CanonicalStructureMapBaseChange.lean`. Its source is Stacks
Tag 08HY's mate construction and Tag 0096's pullback-pushforward adjunction. It is strictly
the map-comparison step of the original argument and introduces no vanishing or
invertibility hypothesis. Three kinds of searches are recorded, including the unavailable
LeanSearch result. No change record is needed because no existing public interface changes.

## Second reading by N4

1. Interface: PASS. Compared both delivered modules with repository sources. The
   existing theorem's statement, visibility, docstring and three public imports are
   byte for byte unchanged (also checked with the project's declaration parser).
   Its only added helper is private and fully proved. The compatibility module is
   new; its theorem has the same verbatim signature as its new node. No existing
   definition, statement, target or other group's module changes.

2. Proof and axioms: PASS as a decomposition. Both modules compiled locally without
   errors or warnings. The original theorem has no direct sorry. The only delivered
   sorry is `AlgebraicGeometry.canonical_structure_map_base_change`, exactly `by sorry`.
   Scratch-copy `#print axioms` reports propext, Classical.choice, Quot.sound and
   sorryAx for the main theorem and the compatibility lemma. The private field helper
   reports only propext, Classical.choice and Quot.sound. No prohibited declaration
   or data definition occurs. In particular no new data is chosen from an open
   existence theorem. Existing imported canonical comparisons remain those of the
   library, and the proof constructs its composites explicitly.

3. Split statement: PASS. The new equation asserts functorial compatibility, with no
   flatness, cartesianness or cohomology assertion. It is strictly the map-identification
   part of the original argument, not a renamed fibre theorem. Reviewed its full
   natural-language proof against the pinned derived unit compatibility and ordinary
   adjunctions, and checked the mate construction in Stacks
   [08HY](https://stacks.math.columbia.edu/tag/08HY) and the adjunction in
   [0096](https://stacks.math.columbia.edu/tag/0096).
   Identity squares give the adjunction unit identity; empty schemes and zero modules
   satisfy the same naturality and triangle equations. The field helper explicitly
   handles both empty and whole opens; an empty fibre cannot meet the invertible
   appTop hypothesis over a nonzero field. Repeated LeanFinder, Loogle and launcher
   grep searches with different words, plus local lean/ searches. No public theorem
   already states the new equation. `moduleBaseChangeMap_algebra` does supply its
   ordinary identity, now cited rather than reconstructed. The existing public
   `canonicalDegreeZeroMateSquare` gives H0 of a counit mate; its full derived helper
   is private, so it is not a direct reusable proof of this new equation.

4. Route and pruning: PASS. Read the proof downward: canonical flat base change gives
   the fibre isomorphism, the existing right-derived nonnegative theorem gives
   vanishing, and degree-zero unit normalization plus the ordinary field calculation
   give the second conclusion after the compatibility equation. Checked the four
   removed original proof imports and all four removed old proof_deps against
   `No longer needed`. None is silently lost. Source import-graph comparison finds
   no removed transitive module; the two additions are the new compatibility module
   and the existing proved flat-invertible base-change module. The repair import
   adds no further transitive module. No global pruning is claimed. Read
   `dag/units/sk-prop-av-cube.json`: its realized statement and sole step are already
   empty in the repository. This delivery leaves them untouched and changes only
   the existing intermediate node's route below the unit, retaining its ancestor
   `lem-sc-flat-derived-structure-unit`; it bypasses no realized unit step.

5. Nodes: PASS after repair. Existing node changes only proof, proof_deps and
   proof_origin. Each proof_deps list is exactly the union of its steps' uses, and
   all referenced nodes exist with their library declarations. The new node has
   source, self-contained statement and statement dependencies, complete proof
   steps, origin, search records, split status, created record, blueprint ancestry,
   chapter/unit and verbatim Lean statement. Added the already proved ordinary
   algebra-compatibility node to its proof plan and recorded second-reader searches.

Second-reading changes: added the missing proof-plan import via
`ModuleBaseChangeMapAlgebra`; made the pending compatibility proof docstring and
node cite its existing ordinary identity and the needed naturality steps; added
search evidence and this review. No compiled proof or theorem signature changed.
One original hole closed, one lower hole added, net zero: decomposition. No globally
pruned module. No change record is needed for these proof-only and new-node repairs.
