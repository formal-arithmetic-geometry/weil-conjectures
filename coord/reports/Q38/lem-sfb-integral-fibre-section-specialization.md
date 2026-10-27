## Worker report

The delivery states `AlgebraicGeometry.ProEtale.IntegralFibreSection.integral_fibre_section_specialization`
in `Sheaf.Paper.IntegralFibreSectionSpecialization`. All theorem proofs are `sorry`.
Every definition has actual construction data. The item statement and proof are unchanged.
This repairs the independent stage-2 return on immutable head `84875dd21abd`, H2.
The saved statement module is retained verbatim; only its DAG dependency ownership is repaired.

Hypothesis-by-hypothesis correspondence:

- Distinct primes p and ell are `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)`.
- The characteristic-p field is `(k : Type u) [Field k] [CharP k p]`.
- The finite norm-topological extension of Q_ell is `(E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]`.
- The algebraic closure with extended norm is `(Ω : Type u) [NormedField Ω]
  [NormedAlgebra E Ω] [IsAlgClosure E Ω]`. No completeness of Ω is assumed.
- The all-continuous condensed coefficients are the existing
  `Profinite.continuousCoefficientRingObj E` and the same construction for Ω.
  These are the equal-universe specializations of the recorded
  `continuousMapRingObjOfUniverse`, retaining every continuous function.
- Internal modules are Mathlib `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1})
  (condensedRingObj Λ X)`. The coefficient object is the recorded pullback from the point.
- The schemes are `X U Z : Scheme.{u}` with their `Over (Spec (.of k))` structures.
  `[IsAffine X] [IsAffine U]` give exactly the two stated affine hypotheses.
  Z is not separately required affine: it is a closed subscheme of affine U.
- The maps are `q : X ⟶ U`, `s : Z ⟶ U`, `i : Z ⟶ X`, with q and s over k,
  `[IsClosedImmersion s]`, and `w : i ≫ q = s`. That equality also forces i to be over k;
  no independent assumption on i is needed.
- The actual test object is `(profiniteToProEtOf X).obj P`, not a formal product.
  `testBase X P` names its actual projection, with explicit scheme endpoints to prevent
  expensive reduction of the comma-category representation. `testProjection q P` is q_P.
- `RootCoordinateFace.testMap i P` is the already published actual induced map i_P.
  `testMap_projection` and `testSection_square` record its two projection identities.
  `fibreSection` is the actual `pullback.lift` into B_P, with components i_P and rho_P.
- `_h : TestHypotheses q s i w` means, for EVERY `P : Profinite.{u}`,
  `IsIntegralHom (testProjection q P)`, `IsClosedImmersion (fibreSection q s i w P)`
  and `Surjective (fibreSection q s i w P)`. The surjectivity hypothesis is not omitted
  or replaced by mere nonemptiness. No finite-type or Noetherian hypothesis is added.
- `GeometricAssertions` quantifies over the supplied module M, with exactly
  `IsLisseCoefficientModule Λ M`, and over every profinite P. This is finite-rank local
  freeness using the dependency definition, with rank zero allowed.

Clause-by-clause correspondence:

- `testComplex Λ M P` is the existing ordinary module pullback L_P placed in degree zero
  using `DerivedCategory.singleFunctor`. The derived direct image is always the recorded
  `CondensedRing.moduleObjectDerivedPushforward`, on the ordinary unbounded derived category.
  `IntegralLisseClosedBaseChange.pull` is exact inverse image applied termwise, and its
  `adj` is the recorded total derived adjunction with its exact left-adjoint identification.
- `specialization` is the actual section-square `exchange` followed by the direct image
  of `boundaryIdentification`. The imported `exchange` is constructed from the actual
  rho-adjunction hom equivalence applied to the canonical square comparison and pulled
  q_P-counit. `boundaryIdentification` is precisely i_P^*L_P[0] ≅ rho_P^*i^*L[0],
  using the single-complex and composition identifications. This defines theta for every
  degree-zero module without a lisseness hypothesis or an invertibility assertion.
- `AdjunctNormalization` spells out the defining rho-adjunct equation with that last
  boundary identification inside the hom equivalence. Thus the comparison is a specified
  map, rather than an arbitrary isomorphism between the two objects.
- `GeometricAssertions` asserts `IsIso (specialization ...)` for the lisse modules, for
  E and Ω separately. Its second conjunct is equality with `factoredSpecialization`.
- `factoredSpecialization` is cartesian exchange for `(q_P,s)`, then
  `R(q_(Z,P))_*` of `(adj Λ a_P).unit`, then `fibreComposition`, then the canonical
  pullback identifications. `fibreComposition` is the conjugate of the actual left
  composition comparison under the actual adjunctions, not a chosen abstract isomorphism.
  `fibreSection_fst` and `fibreSection_snd` name the two defining lift identities.
- `DegreeZeroRestriction` states equality of H^0(theta), after the canonical single,
  exact-pullback/H^0 and left-exact-right-derived/H^0 identifications, with
  `ordinaryRestriction`. The latter is the actual ordinary-adjunction mate of the
  ordinary square comparison and ordinary q_P-counit: restriction of full-source sections.
- `PointNormalization` treats every singleton profinite parameter (in particular *).
  `originalBoundary` is s^*Rq_*M[0] → i^*M[0], defined by i^* of the actual counit.
  `originalToTest` uses the actual test-projection unit and canonical composition map.
  The statement says the source comparison and rho-unit are isomorphisms and gives
  `originalToTest ≫ specialization = originalBoundary ≫ rho-unit`.
  Thus terminal normalization uses the actual test schemes and their canonical maps.
- `Naturality` applies `CubeNaturality` to every actual test-section square and every
  degree-zero module. The cube formula requires `WeaklyEtale v` for the base map, includes all six
  face commutativities, and has an
  arbitrary compatible full-source module arrow. Both paths are explicit exchange
  composites with the canonical square transports. Taking the geometric cube to be
  the identity gives module naturality. Continuous maps of parameters give the maps
  on actual test schemes. Cartesian pro-etale base change is another substitution.
- The same cube quantifies over entire schemes. For families, use the source
  X[Q×P], target X[Q×P'], bases U and U[Q], and section bases Z and Z[Q]. The maps
  induced by `(q,p') ↦ (q,phi(q,p'))` for a continuous Q×P'→P satisfy those cube
  identities by the recorded finite-limit/test-object construction. The equation
  is over the whole Q-parametrized schemes; no parameter point is chosen or tested.
- `testScalarUnit` uses the actual ordinary tensor unit on X, embedded in degree zero,
  then exact pullback to X[P], the canonical pullback/restriction comparison, and
  the canonical single-complex comparison. Its target is restriction of the actual
  pullback of the ordinary scalar extension of M on X. It is not a separately supplied map.
- `restrictedBoundaryIdentification` transports the restricted Omega test module to
  rho_P^*i^*Res(M_Omega[0]) through the actual restriction/pullback comparisons.
- `ScalarCompatibility` asserts two explicit equalities for every lisse M and P.
  The first is module naturality for `testScalarUnit`, with the common boundary
  transport appended. The second is the directional restriction square for the
  Omega exchange, with that identical boundary transport appended. The shared vertex
  is `s^*Rq_(P,E),* Res(M_(Omega,P)[0])` and the shared boundary target is
  `Rrho_(P,E),* rho_P^*i^*Res(M_Omega[0])`. The directional comparisons enter this
  vertex in their canonical direction; none is inverted. These are the two squares
  forming the specified cospan. No scalar-extension/direct-image isomorphism is asserted.

Dependency interfaces read and used:

- `Sheaf.Topology.ContinuousMapCondensedRing`: `Profinite.continuousMapRingObjOfUniverse`,
  the actual all-continuous ring sheaf and its pointwise ring structure.
- `Sheaf.Topology.ContinuousMapCondensedRingMap`: `continuousMapRingObjMapOfUniverse`;
  the existing `IntegralLisseClosedBaseChange.coefficientInclusion E Ω` uses it.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `profiniteToProEtOf`; the actual point pullback and actual tests.
- Mathlib `CategoryTheory.Mod`, `AlgebraicGeometry.Scheme.ProEt`,
  `AlgebraicGeometry.IsClosedImmersion`, `AlgebraicGeometry.IsIntegralHom`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: `moduleObjectDerivedPushforward`;
  the original total K-injective derived direct image, not an abelian-sheaf substitute.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`: `Mod.extendScalars`,
  `Mod.comap`, `Mod.extendRestrictAdjunction`. No private copy of scalar extension.
- Definition dependency `def-sfb-derived-exchange-scalar-comparisons`, existing module
  `Sheaf.Paper.IntegralLisseClosedBaseChange`: `pull`, `adj`, `pullComp`, `square`,
  `exchange`, `restrict`, `restrictPull`, `restrictPush`, `scalarUnit`, `coefficientInclusion`.
- Definition dependency `def-sfb-test-map-derived-composition`, existing module
  `Sheaf.Paper.RootTowerCoordinateFace`: its already existing generic `testMap` and
  canonical `lowerComp`; the coordinate-face theorem itself is not assumed in the conclusion.
- Definition dependency `def-sfb-right-derived-single-h0-comparisons`, existing module
  `Sheaf.CategoryTheory.RightDerivedSingleH0`: `Functor.singleRightDerivedH0Iso` and
  `Functor.mapSingleRightDerivedH0Iso`, the canonical degree-zero identifications.
- All available recorded proof-dependency modules are imported with proof visibility,
  except the three modules needed publicly for the interfaces just listed. These retain
  the node's exact open/closed calculus, internal-module transport, ring-sheaf-change
  adjunction, Grothendieck and adjunction-normalized derived composition inputs.
  The three definition nodes depend only on definitions and introduce no dependency cycle.
  The original proof dependency on integral closed base change remains a proof dependency.

Edge cases checked before writing: P empty makes the actual tests empty; Z empty makes
both boundary objects zero; M zero is allowed, including lisse rank zero. For a singleton
P the actual projection comparisons are isomorphisms and the normalization is the actual
boundary restriction. The identity diagram is included. No finite parameter, chosen
parameter point, boundedness of complexes, connectedness, nonempty scheme, uniform
nilpotence exponent, or completeness of Ω occurs in the hypotheses. A nonsurjective
closed inclusion into a nonempty fibre is correctly excluded by `TestHypotheses`.

Searches for existing statements/definitions:

- msearch LeanFinder: “Derived specialization from integral direct image to a surjective
  closed fibre section, counit adjunct and compatibility with coefficient restriction”:
  eight unrelated specialization/stalk results, no such derived module statement.
- msearch Loogle: `Adjunction.homEquiv, IsClosedImmersion, IsIntegralHom`: no hits;
  the service reports that its unqualified `Adjunction.homEquiv` identifier is unknown.
- msearch grep: `fibreSection|fibre_section|sectionSpecialization|section_specialization`
  in Mathlib/AlgebraicGeometry: no hits.
- msearch LeanSearch: “An integral morphism and a surjective closed immersion section of
  a closed fibre induce a canonical derived specialization isomorphism for lisse
  continuous coefficient modules”: eight basic integral/closed-immersion results,
  no condensed derived specialization.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for fibre-section, specialization,
  section-specialization, boundaryRestriction and fullSource: the integral geometric
  fibre-section lemmas concern discrete coefficients or local lifts/zero detection;
  RootBoundaryComparison and RootTowerCoordinateFace are the specialized root setting.
  The generic canonical testMap and composition map are reused from the latter;
  none states this node with its arbitrary integral source and coefficient cospan.
- Exact item-id search in the source root has no match. No existing declaration states
  the full item, so `existing: true` would be incorrect.

No statement correction or dependency module is needed. Three new definition nodes
record the existing reusable constructions previously cited through theorem nodes.
The item-specific maps and comparison predicates remain in its `lean.declarations`,
with their source docstrings.

Validation: `scompile.py` compiled the complete module cleanly in sandbox mode (19.4 s)
and library mode (18.6 s), within the unchanged 60-second per-file limit. The earlier
ordinary-comparison timeout was repaired by caching the generic ordinary square/mate
and importing its canonical upstream congruence map. No launcher or library file was edited.


## Repair of return H2

The return identifies three theorem nodes added to `stmt_deps` only to access their
plain helper definitions. Removed `lem-sfb-integral-lisse-closed-base-change`,
`lem-sfb-root-tower-coordinate-face`, and `lem-kun-right-derived-single-h0` from
those added statement dependencies. Replaced them by the three definition nodes below.
Their records have `existing: true`, no `file`, and explicitly list every reused
construction. The existing source modules and the delivered Lean module are unchanged.
The original eleven statement dependencies are retained in order. The item's
statement, proof, proof dependencies, source and all remaining base fields are unchanged.
Thus the main theorem's signature, the canonical map and all reviewed clauses are retained.
The first dry run of the saved packet passed at `46632d6b9b6`; that mechanical pass
did not discharge this independent H2 return, so the dependency repair was still made.
The wrappers refresh/rebase the delivery on the live branch; no direct Git command was run.

## New nodes

`def-sfb-derived-exchange-scalar-comparisons` owns the already constructed exact pullback,
actual derived adjunction, pullback composition and commuting-square comparisons,
exchange, coefficient restriction and its pullback/direct-image comparisons, ordinary
scalar unit in degree zero, and continuous coefficient inclusion. Its existing module is
`Sheaf.Paper.IntegralLisseClosedBaseChange`. The main declaration is `exchange`; its
`lean.declarations` lists `pull`, `adj`, `pullComp`, `square`, `exchange`, `restrict`,
`restrictPull`, `restrictPush`, `scalarUnit`, and `coefficientInclusion` in the namespace
`AlgebraicGeometry.ProEtale.IntegralLisseClosedBaseChange`. These are real definitions;
no integral closed-base-change theorem is assumed to define them. The definition is the
adjunct in the item's source place, with the scalar comparisons in their actual directions.

`def-sfb-test-map-derived-composition` owns the existing generic actual test-scheme map
and adjunction-normalized derived composition comparison in
`Sheaf.Paper.RootTowerCoordinateFace`. Its main declaration is
`AlgebraicGeometry.ProEtale.RootCoordinateFace.testMap`; its declaration list also records
`test`, `Modules`, `upper`, `lower`, `adjunction`, `upperComp`, and `lowerComp` in that
namespace. The definition uses only the test-object construction and actual module
push/pull and adjunctions, with no root-tower or coordinate-face theorem. The source
place is the induced i_P and canonical composition identifications in the item's
full-source specialization and singleton normalization.

`def-sfb-right-derived-single-h0-comparisons` owns the two existing definitions
`CategoryTheory.Functor.singleRightDerivedH0Iso` and
`CategoryTheory.Functor.mapSingleRightDerivedH0Iso` in
`Sheaf.CategoryTheory.RightDerivedSingleH0`. They are respectively the canonical
H⁰-to-R⁰-to-underived isomorphism and that comparison after an exact additive functor.
The source place is the item's degree-zero clause; the generic construction uses the
injective-resolution comparisons described in Stacks Tag 05TD. The node asserts no
augmentation normalization theorem and assumes precisely the abelian, derived-category,
enough-injective/K-injective and exactness data needed by these definitions.

For each new node the same three fresh Mathlib searches were run: LeanSearch for
“Canonical derived exchange for internal condensed modules via adjunction, functorial
profinite test schemes, and zeroth homology comparison for right derived functors”
returned eight results including `Functor.rightDerivedZeroIsoSelf` (one constituent
of the H⁰ composite); LeanFinder for “Canonical adjunction exchange and restriction of
scalars for derived sheaves, induced maps of profinite test schemes and degree zero
right derived functor identification” returned eight ordinary sheaf/condensed adjunction
results; msearch grep for
`singleRightDerivedH0Iso|mapSingleRightDerivedH0Iso|profiniteToProEtOf|IntegralLisseClosedBaseChange`
returned no Mathlib hits. The exact outcomes are copied into each node's `mathlib_searches`.
The rg search of `dag/nodes` found these constructions recorded only among helper
names of the three theorem nodes, with no definition owner; source rg found the exact
existing project definitions, which these new nodes reuse without copying them.
`blueprint_refs.py search` returned zero matches for “right-derived single”, “test-scheme”
and “derived exchange scalar”. The ancestor tool returns null, which the new records
retain; their `via` prepends this item to its inherited path. All new nodes are in the
item's chapter/unit, have empty proof/proof_deps and none lean_audit, and are directly
cited in its repaired `stmt_deps`.

## Second reading by Q38

This is a separate reread by this worker; the dispatcher forbids starting other agents.
The maintainer's independent immutable-head review has already checked the mathematics
and returned only H2. I reread the saved module and the dependency definitions, keeping
that approved mathematical content unchanged. `TestHypotheses` still universally binds
P and requires integral q_P, closed a_P and surjective a_P. The main theorem still
binds distinct p and ell, the characteristic-p field, finite normed E extension,
normed algebraic closure Omega, affine X and U, closed s, and the equation i ≫ q = s.
`GeometricAssertions` retains both invertibility of the actual specialization and its
factorization; `AdjunctNormalization` retains the actual rho-adjunct of the pulled
q_P-counit; `DegreeZeroRestriction` retains the two named H⁰ comparison definitions;
`PointNormalization` retains the actual test-comparison and rho-unit isomorphisms and
its boundary equation. `Naturality` still quantifies over the full cube and compatible
module map, so identity, parameter and whole Q-family cases remain covered.
`ScalarCompatibility` still has the ordinary tensor unit and two forward restriction
equalities with a common boundary target. Empty P, empty Z, zero module and rank zero
are still allowed. No stronger hypothesis or weaker conclusion was introduced.

I read each new definition record against the full signature/docstring and construction
of its existing declarations. The exchange/scalar node describes the actual mates;
the test/composition node describes the actual pullback lift and conjugate isomorphism;
the H⁰ node describes the actual two canonical comparison composites. Compositional
order in the TeX was checked against the source functor signatures. Their declarations
are plain definitions/abbreviations, without `.choose` from any of the three dropped
theorems. The H2 defect is repaired in the DAG without changing Lean constructions.

Repair validation: `scompile.py` compiled the unchanged module cleanly in sandbox mode
(14.6 s) and library mode (15.6 s). The item/base field comparison confirms that only
`lean` and `stmt_deps` differ; no original statement dependency was removed. Each new
node's cited definition ids exactly match its `stmt_deps`.

The repaired-packet dry run required each definition citation to have its own brackets;
the two grouped citation lists in the new nodes were expanded to individual `[id]`
citations, preserving their dependencies and mathematical text.
