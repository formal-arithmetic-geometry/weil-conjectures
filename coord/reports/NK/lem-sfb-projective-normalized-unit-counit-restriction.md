## Worker report

The module `Sheaf.Paper.ProjectiveNormalizedUnitCounitRestriction` states
`AlgebraicGeometry.ProEtale.RationalP1.projective_normalized_unit_counit_restriction`.
Its sole proof is `sorry`. One computational wrapper `RestrictionExact` bundles the existing exactness data.
No dependency repairs, new nodes, or statement corrections are needed. The JSON changes only `lean`.

Hypothesis and conclusion correspondence:

- The arbitrary condensed coefficient is `Λ : Sheaf (coherentTopology Profinite.{u})
  Ab.{u + 1}` with `MonObj Λ` and `IsCommMonObj Λ`. This is the unbundled ring-object
  encoding of `Profinite.CondensedRing`, not a topologically presented special case.
  `Modules Λ X` uses exactly `condensedRingObj Λ X`, the pulled-back coefficient.
- `Y : Scheme.{u}`, `ProjectiveLine Y`, `diagonalSurface Y`, `diagonalImmersion Y`,
  `firstProjection Y`, `secondProjection Y`, and `ProjectiveLine Y ↘ Y` are the recorded
  projective line, self-product, diagonal, projections, and structure map. None is
  replaced by an arbitrary object or map.
- `IsClosedImmersion (diagonalImmersion Y)` states closedness. `U`, `j`,
  `IsOpenImmersion j`, `QuasiCompact j`, and `hj` specify its quasi-compact complementary
  open: the equality is of the ranges of the underlying topological maps.
- The four `PreservesFiniteLimits`/`PreservesFiniteColimits` binders express exactness of
  the two coefficient-module inverse images. Their additivity is supplied by the
  existing `upperStar_additive` instance. In this pulled-back coefficient setting the
  published framework already proves these exactness properties; the binders explicitly
  retain the assumptions the node requests, rather than introducing another condition.
- `L : ∀ X : Scheme.{u}, Modules Λ X` specifies the coefficient modules. `d : Diagram Λ Y L`
  retains the fixed class `delta`, normalized derived models, traces and integration
  equalities. `e` is precisely pullback of the degree-zero `L_P` shifted by positive two
  along the second projection, isomorphic to degree-zero `L_W` shifted by positive two.
- `P`, `Q` are object properties on the ordinary unbounded internal-module derived
  categories of the projective line and base. Their `FullSubcategory` types are full;
  `IsClosedUnderIsomorphisms` is repleteness and `IsTriangulated` is the triangulated
  subcategory hypothesis. No boundedness, constructibility, localizing, rational,
  characteristic or base-field hypothesis is added.
- `hF` and `hG` express preservation by the specified ambient functors. `F`, `G`,
  `hF_eq`, `hG_eq` name exactly their full-subcategory lifts. These are names for prescribed
  restrictions, not additional choices of maps or unrelated functors. The composite in
  `hG_eq` is pullback followed by `twist`, namely `(A ⊗ᴸ L_P)[2]`.
  `hF_exact : RestrictionExact P Q F` and `hG_exact : RestrictionExact Q P G` express
  their stipulated exactness. This wrapper is defined with real data as existence of
  the existing `CommShift ℤ` structure with the existing `IsTriangulated` property.
  It elaborates these structures over abstract ambient categories before specialization;
  it does not introduce another definition of exactness. In Mathlib a triangulated
  functor is automatically additive. The local `letI` appears only in the helper
  definition, never in the theorem signature. Stage 3 can extract its two fields.
- `hI` uses the recorded `UnitInversionCondition` for every object of `P`: it is exactly
  invertibility of the fixed exchange and twisted projection. `hJ` uses the recorded
  `CounitInversionCondition` for every object of `Q`: exactly the fixed left projection.
- The first conjunct exhibits a natural isomorphism from first pullback followed by
  tensoring on the right with the derived supported coefficient, to diagonal
  pushforward. Its component equation is equality to the actual `diagonalTensorMap`.
  Thus this asserts the canonical map is a natural isomorphism on *all* unbounded
  `D(P)`, rather than merely the existence of some unrelated isomorphism or only
  invertibility on the subcategory.
- The second conjunct is `Nonempty (RΔ_* ⋙ Rp₂_* ≅ 𝟭 _)`. Composition order is Lean's
  left-to-right functor composition, hence this is exactly `Rp₂_* RΔ_* ≅ 1`.
- The last conjunct is a single `∃!` over a pair of natural transformations
  `(𝟭 P.FullSubcategory ⟶ F ⋙ G) × (G ⋙ F ⟶ 𝟭 Q.FullSubcategory)`.
  `UnitComponentNormalized` and `CounitComponentNormalized` apply to their underlying
  components `(a.1.app M).hom` and `(a.2.app K).hom`. These predicates quantify only
  invertibility proofs and assert heterogeneous equality to the fixed whole ambient
  formulas. Uniqueness is for this predicate, not for all natural transformations.
  Naturality is part of the two natural-transformation types, and their endpoint
  functors are the specified exact lifts and their composites. No triangle identities
  or assertion of an adjunction is included.

Dependency declarations read and reused (all names below are in
`AlgebraicGeometry.ProEtale`, with the displayed subnamespace):

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, and preservation of commutativity.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: `CondensedRing.moduleObjectDerivedPullback`
  and `CondensedRing.moduleObjectDerivedPushforward`, with the publicly imported adjunction.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`: the native closed
  derived tensor/Hom structure on internal modules.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `AlgebraicGeometry.ProjectiveSpace`;
  the projective line and diagonal are the existing framework's specializations.
- `Sheaf.Paper.DiagonalCoefficientCategory`: `DiagonalCoefficients.Modules`, `unit`, `Diagram`.
- `Sheaf.Paper.ProjectiveDiagonalComposition`: `RationalP1.pushSectionIso`, supported unit
  comparison, and normalized left projection.
- `Sheaf.Paper.RationalP1DiagonalTensor`: `RationalP1.diagonalTensorMap`, its inverse
  isomorphism and naturality; the canonical `square` is retained through the inversion API.
- `Sheaf.Paper.TateTwistedProjection`: `RationalP1.twist`, `tensorShiftIso`,
  `twistProjectionMap`, and the uniquely normalized projection mate.
- `Sheaf.Paper.RationalP1AmbientComposites`: `RationalP1.unitComponent`, `counitComponent`,
  `UnitComponentNormalized`, `CounitComponentNormalized`.
- `Sheaf.Paper.RationalP1UnitInversionCondition`: `RationalP1.UnitInversionCondition`.
- `Sheaf.Paper.RationalP1CounitInversionCondition`: `RationalP1.CounitInversionCondition`.

All recorded statement modules are public imports. Recorded proof modules, including the
Mathlib match `CategoryTheory.Functor.mapDerivedCategory` in
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, are plain imports where not already
statement imports. The docstring follows the node's eight proof steps, including the
naturality in the pushed variable of the projection mate; this does not confuse it with
left-projection naturality in its other variable.

Searches (2026-10-27):

- `msearch.py ... leanfinder "Unique normalized diagonal unit and trace counit on full
  triangulated subcategories with invertible exchange and projection maps"`: eight
  generic triangulated adjunction/equivalence hits; none states this conditional
  component-normalized pair without triangle identities.
- `msearch.py ... loogle "CategoryTheory.NatTrans.ext"`: exact generic extensionality
  lemma; it does not give the projective-line construction.
- `msearch.py ... grep "UnitComponentNormalized|CounitComponentNormalized|restrictedUnitCounit"`:
  zero Mathlib hits.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  the item ID, `restrictedUnitCounit_existsUnique`, and the proposed declaration name:
  no existing public statement of this node. `RationalP1UnitCounit.lean` contains a
  *private* generic `restrictedUnitCounit_existsUnique` and a public theorem specialized
  to rational coefficient/localizing categories. The private statement omits the
  diagonal-isomorphism conclusions; neither is an exact public match for this node.
  Existing public normalization definitions and diagonal-map declarations are reused.

Edge cases checked: the empty base scheme is allowed; no points, nonemptiness or finite
type condition is assumed. Zero modules and zero subcategories are allowed. An empty
object property is already ruled out by the node's triangulated-subcategory requirement
(`ContainsZero`), not by an extra assumption. All complexes are unbounded; there is no
cohomological degree restriction. The coefficient can be any commutative condensed ring,
including the zero ring. No arbitrary inversion choice affects the formulas, since the
inversion witnesses are proofs. Site/abelian-sheaf universes remain `u`/`u+1` as in the
recorded internal-module framework. No node fault or disputed statement was found.

## Second reading by NK

Author's separate second pass against the node and the completed file: the conjuncts
retain the canonical map (component equality), the pushforward composite, and uniqueness
of the normalized pair. The two transformation directions were checked using Lean's
composition convention: `F ⋙ G` acts on the projective-line category, and `G ⋙ F` on the
base. Both inversion conditions quantify over the correct subcategory. Repleteness,
triangulatedness, preservation, exactness, the complementary-open equality, fixed `d`,
and fixed `e` are explicit. The heterogeneous normalization API is reused without
unfolding or rebuilding the tensor data. No strengthening to triangle identities was
made. The first compile reached the statement and exhausted the default 200000 heartbeat budget
while elaborating the concrete triangulated-functor assumptions (20.3 seconds). A temporary
800000-heartbeat retry confirmed expensive unfolding: the same location exhausted that
budget (77.9 seconds). The retry also warned against an unscoped heartbeat option. That
option was removed. `RestrictionExact` now bundles exactly the same shift and triangle
preservation structures over generic ambient categories, then specializes the bundle in
the theorem; this avoids repeatedly elaborating the concrete full-subcategory structures.
No time limit or transparency setting is relaxed. No mathematical hypothesis changed.
Independent review is performed
by the maintainer, as specified by this worker's dispatch brief.

Validation: `scompile.py` succeeded without warnings or errors. The sandbox probe took
8.2 seconds and the actual library-module compile took 10.4 seconds. The theorem proof
remains `sorry`; `RestrictionExact` is an explicit definition with no postponed data.
