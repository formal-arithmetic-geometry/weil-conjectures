## Worker report

The module `Sheaf.Paper.PointSystemPowerRoosCoherence` states
`WeilConjectures.PointSystemTransport.PowerRoos.point_system_power_roos_coherence`.
Its only postponed proof is this named theorem. The normalization predicates
are included in its conclusion, rather than assumed as extra hypotheses. Its docstring contains the complete
seven-step proof from the node. All other declarations are transparent abbreviations,
actual compositions, actual coordinate maps, or structures packaging the specified
maps and their normalization equations. There is no choice of unspecified data.

Source read: main-20261015, trace-transport Global powers, and
`sec-trace-formula/sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md`,
part (3), together with the node's explicit strict-system/Roos refinement. The
refinement records Stacks 03CB, 0H7J and 0941 and distinguishes whole-system morphisms
from their evaluations. The original node statement is unchanged.

Clause-by-clause correspondence:

- The fixed finite-field/algebraic-closure datum is `D : FiniteFieldDatum.{t}`.
  The coefficient prime, finite extension and different characteristic are
  `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
  `[FiniteDimensional ℚ_[l] E]`, and `hl : l ≠ D.p`. The existing Padic coefficient
  quotient rings use the chosen uniformizer and `coefficientExtensionIdeal`.
  Site and coefficient universes `t,u` are independent; all module sizes are
  the existing `max u (t+1)` sizes. A level `n : ℕ` means exponent `n+1`, exactly
  as in the dependency interfaces. No separated finite-type auxiliary scheme is
  needed at this point, and none is imposed as an extra hypothesis.
- The point `s` is `Spec (.of D.k)`. The automorphism and its powers are the
  recorded `pointPower D r`, recursively formed from `frobeniusPointIso D`, hence
  the Spec of geometric Frobenius. All coefficient sheaves and their limit are
  the recorded constructions used by `inverseImageIntegralModules`.
- The strict abelian system category is `coefficientSequenceModules l E s`,
  namely module sheaves on the actual ringed sequence site. Its ordinary
  unbounded derived category is `coefficientSequenceDerived l E s`. There is no
  normalized/cartesian subcategory, no tower of separate derived categories,
  and no boundedness or constructibility restriction.
- `coefficientSequenceRestriction` is precisely U_s, retaining the quotient-linear
  transitions. `Uc` is its termwise complex functor. `coefficientSequenceLimit`
  is precisely L_s=Rlim U_s, using `coefficientConstantTowerLimit` after the exact
  restriction. These are used directly, not redefined as new categories or limits.
- `F r` abbreviates the recorded completed-module inverse image
  `inverseImageIntegralModules l E (pointPower D r).hom`, whose action uses the
  canonical coefficient-limit map. `Fc`, `Ft` are its ordinary complex and tower
  functors. `Gc r` is the recorded whole-system `pull` applied termwise.
- `Compositors.d` and `.t` have the orientations F_1 F_m → F_(m+1) and
  G_1 G_m → G_(m+1). Functor composition is written in execution order in Lean,
  so their sources are `F m ⋙ F 1` and `pull m ⋙ pull 1`. `HasSiteSections` and `HasSystemSections`
  equations fix them as the identity on the twice-reindexed original section.
  `HEq` only expresses transport between canonically equal site-object carriers;
  it does not identify arbitrary isomorphic sheaves.
- `Compositors.b` identifies actual U_s G_r with levelwise F_r U_s; its
  `HasRestrictionSections` equation is the identity on every original section at every level.
  This fixes the completed scalar restriction through the original projections.
- The finite j_r are exactly `inverseImageFiniteComparisonComplex`, not chosen
  isomorphisms. `Compositors.tensor` and `HasTensorUnits` express that the compositor
  sends the two successive j insertions, i.e. `(x ⊗ 1) ⊗ 1`, to the direct
  `x ⊗ 1`. Both finite modules, every integer degree, every site object, and
  every source section are quantified. The x,x' HEq premise just supplies the
  canonical direct/nested reindexing identification. Since j is invertible and
  the tensor compositor is module-linear, these equations specify the canonical
  tensor pullback-composition map, in the inverse orientation of Tag 0D6D.
- The node's u is the recorded `chainTransport`, followed only by the
  canonical `mapHomologicalComplexCompIso` to factor its target as G_r then sections. The first conjunct is
  its equality as a chain map in the category of entire R-module towers. The
  target compositor is `complexSections.map (tc.hom.app M)`. Naturality of this
  map includes all the original transition and differential squares.
- `I` is the recorded `derivedTransport` followed only by the canonical
  `mapDerivedCategoryCompIso` to display its target as G_r then derived sections.
  `td` is the canonical localization of t. The second conjunct is the required
  equality for every object C of the ordinary derived SYSTEM category.
- `RoosNormalization.ordinary` is pinned by every limit projection. Its `.unit`
  is natural and normalized on every K-injective tower using the actual
  `rightDerivedFunctorObjQIso`. Its `.theta` identifies total limit with the
  actual existing `roosF`; `.theta_normalization` sends this unit to `Q(roosι)`.
  This pins the normalized total-limit identification, including its sign.
- The cone H is the existing `CategoryTheory.roosF`, the shifted cone of the
  original `towerTransitionEndomorphism`. `coordinates` applies the canonical
  shift/cone coordinates `roosχ`, the biproduct interchange, and `diag(1,-1)`.
  Thus they are exactly the signed coordinates (x,y) of the node, with
  D(x,y)=(dx,(1-s)x-dy), not an independently supplied cone or differential.
- `HasProducts` pins the product comparison by every original
  product projection, followed by the identity-on-sections coefficient transport b.
  `HasFirstCoordinate` and `HasSecondCoordinate` use this same psi on the unshifted and shifted
  coordinates respectively. Their right sides depend on only the corresponding
  coordinate, so both off-diagonal components are zero.
- `Comparisons.a` is a natural derived isomorphism on the whole system category.
  `HasDerivedModel` pins it on EVERY strict representative, through the actual exact
  localization factors and `toRoos`, as theta inverse, kappa, F(theta). It is
  not an arbitrary natural isomorphism or a hypothesis on C.
- The third conjunct gives compositor equality on entire product complexes with
  `roosPmap` applied to the actual U_s(t). The fourth gives equality on the
  entire cone, using the same kappa. The fifth is exactly
  a_(m+1) d_m = L_s(t_m) a_1 F_1(a_m), written in Lean composition order.
  The five equality predicates,
  `StrictTransportCoherence`, `DerivedTransportCoherence`, `ProductCoherence`,
  `ConeCoherence`, and `DerivedComparisonCoherence`, are conjoined and quantify `m` with `hm : 1 ≤ m`; the strict clauses quantify
  every unbounded M, and the derived clauses every C. Naturality for derived
  morphisms is part of the natural isomorphisms a,d,t and transformations I.
  No claim that derived evaluation detects equality is made.

The theorem existentially packages the canonical maps and their specifications,
rather than assuming them as free hypotheses. The normalization equations fix their
values on all sections and product coordinates, and the localization/derived-unit
normalizations fix the derived maps. This matches the node's instruction to specify
a by these constructions. Nothing is extracted using choice from mere existence.

Dependency declarations read and used (the statement dependencies are public imports;
proof-only dependencies are plain imports):

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`; its existing finite-field
  and Padic quotient conventions are used at the point.
- `Sheaf.SixFunctors.SchemeFrobenius`: `FiniteFieldDatum.schemeFrobenius` and the
  recorded geometric-Galois map; its point specialization is `frobeniusPointIso`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, reexporting the original completion,
  projections and coefficient rings at independent site/coefficient universes.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `SemilinearSections.semilinearDerivedSections`, ordinary strict-system framework.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus`, and its imported
  `coefficientSequenceRestriction`, `coefficientSequenceLimit` and tower limits.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `Scheme.isoSectionwiseInverseImage_equivalence`,
  `isoSectionwiseModuleInverseImage` and its exactness instances.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`:
  `ProEtale.inverseImagePullbackComparisonDerived`, reexporting
  `inverseImageIntegralModules`, coefficient maps and
  `inverseImageFiniteComparisonComplex`, precisely the finite j's used here.
- `Sheaf.Paper.CoefTowerCoaugmentation`: `CoefTower.adjunction`, ordinary tower
  and constant-scalar conventions, retained through the existing transport module.
- `Sheaf.Paper.PointProEtaleSectionsExact`:
  `ProEtale.point_proEtale_sections_exact`, exact sections used by the recorded transport.
- `Sheaf.Paper.PointSystemTransportDescent`:
  `pointPower`, `pull`, `sections`, `chainTransport`, `derivedTransport`,
  `tensorPull`, `finiteComparison_inverse`, and `point_system_transport_descent`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `integralTowerGeneralPullbackComposition`, `integralFinitePullbackModel` and
  `integralFiniteCanonicalPullbackComposition`; these fix the finite tensor
  interpretation and composition direction, used in the proof plan.
- `Sheaf.CategoryTheory.StrictRoosComparison`: `CategoryTheory.strictRoosComparison`,
  normalized natural total-limit identification, ordinary inclusion and strict maps.
- `Sheaf.Paper.ExactProductFunctorStrictLimit`:
  `CategoryTheory.exactProductFunctorStrictLimit`, signed cone normalization and
  canonical product comparison on both coordinates, with its derived identification.
- Added already-landed statement dependency `def-weil-strict-roos-model`:
  `Sheaf.CategoryTheory.StrictRoosModel`, `CategoryTheory.roosF`, `roosχ`, `roosP`,
  `roosPmap`, `roosι`, `roosLimitFunctor`. This avoids a private copy of the cone.
- `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle`:
  `Functor.mapDerivedCategoryCompNatIso`; Mathlib's
  `Functor.mapHomologicalComplexCompIso` gives the termwise compositors.
- Proof imports: `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`
  (`Scheme.proEtaleCoefficientInverseImageMap_comp`),
  `Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus`
  (`Scheme.pointSheafInsertionCalculus`),
  `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
  (`Scheme.ProEt.countableProducts_exact`),
  `Sheaf.Paper.ExactProductFunctorRoosChainMaps`
  (`CategoryTheory.exactProductFunctorRoosChainMaps`).

Edge cases checked: m=1 is included, and the direct power is 2; the auxiliary
functors/comparisons also make sense at power zero. The first finite level is
exponent 1, so no zero quotient level replaces it. Zero modules, zero towers and
zero unbounded complexes use the same section/product maps and normalized units.
All integer degrees, nontrivial quotient transitions and arbitrary derived
morphisms remain present. No assumption that the realized N is constructible,
bounded, derived-complete, normalized, or fixed by Frobenius is added.

Searches actually run via msearch.py:

- LeanFinder: "Point transport along powers of geometric Frobenius composes on strict
  coefficient systems and the canonical product comparison on both Roos cone coordinates
  respects composition". Eight hits, mostly LightProfinite transitions,
  localCohomology.diagramComp and a GrothendieckTopology cone-evaluation lemma;
  none state the system transport plus whole-cone/derived compositor assertion.
- Loogle: `CategoryTheory.Limits.piComparison, CategoryTheory.Functor.map_comp`:
  zero hits.
- Mathlib grep: `piComparison_comp|pointTransport.*comp|Roos.*compositor`:
  fourteen hits. Relevant product-projection lemmas were read in Shapes.Products
  and Preserves.Shapes.Products; they specify projections but do not state this result.
- LeanSearch: "Canonical product comparison for exact inverse image commutes with
  composition on both summands of the Roos cone": eight hits including
  `inv_piComparison_comp_map_π`, `prodComparison_inv_natural`, and unrelated convex
  cone/comap lemmas. These are ingredients, not a match.
- Repository rg: `lem-trf-point-system-power-roos-coherence|point_system_power_roos_coherence`
  in `lean/WeilConjectures` and `lean/Sheaf`: no existing declaration.
  Broader power/composition/Roos searches found the dependency insertion calculus,
  strict Roos model, generic exact-product comparisons, and other completion
  coherence theorems with different inputs. Those use different operations and
  are not the point-system theorem here. No duplicate notion was created.

No statement correction, disputed mathematical assertion, new definition node, or
dependency-record repair is needed. The one added stmt_dep is an already recorded
and landed definition actually used in the signature.

## Second reading by Q01

In-session second pass, with the node statement and completed module open; no separate
agent was started, as the dispatcher explicitly prohibited delegation. The check
matched both coefficient universes, positive exponents, the original strict-system
category and all five equations. It checked Lean's execution order F_m then F_1
against mathematical F_1 F_m, the orientation of theta, and the inverse orientation
of finite pullback composition. It checked that both signed cone coordinates are
fixed, not just their evaluation on cohomology. It also checked that the main result
constructs the normalized comparisons instead of assuming compositor coherence,
and that I is the existing descended insertion with its canonical target factoring.
A field-access typo was repaired, and the tower complex comparison uses the actual
`complexOfFunctorsToFunctorToComplex.map` on morphisms. The normalization predicates were separated from record fields and canonical chain
functor targets were factored explicitly to avoid expensive implicit unfolding. No mathematical
clause or hypothesis was altered in that pass. Independent maintainer review remains
the delivery's external mathematical review, as specified by the brief.

The five equality predicates package the displayed equations without changing them;
they are transparent definitions belonging to this node. All normalization predicates
are asserted in the conclusion of the theorem. Keeping these signatures separate avoids
repeated unfolding in dependent record eliminators; the module is still compiled as
one file under the normal 60-second limit. The auxiliary `u` and `I` only apply the
canonical complex/derived target factorizations to the recorded transport maps.

### Clause-by-clause reading (added at maintainer review, H11)

The paragraphs above did not match each hypothesis and clause of the node with its
Lean. This list does. The Lean, the node and every other record are unchanged.

Objects and hypotheses:

- k_0 = F_q, k its algebraic closure: `D : FiniteFieldDatum.{t}`, with point `Spec (.of D.k)`.
- ℓ prime, ℓ ≠ char k: `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`. `hl` is needed because
  `chainTransport` and `derivedTransport` take it. No further hypothesis is added.
- E/Q_ℓ finite, R, ϖ, A_n = R/ϖ^n for n ≥ 1: `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
  `[FiniteDimensional ℚ_[l] E]`. Level index n means exponent n+1, as in every
  dependency interface. The universes t and u are independent.
- h = Spec(γ), with powers h^r: `pointPower D r`, defined recursively from
  `frobeniusPointIso D` (descent node).
- B_n, R̂_s and S_s with its unbounded D(S_s): `coefficientSequenceModules`,
  `coefficientSequenceDerived` (strict systems on the ringed sequence site, with no
  cartesian or bounded restriction).
- U_s and L_s = R lim U_s: `coefficientSequenceRestriction` and `coefficientSequenceLimit`.
  `Uc` is the termwise U_s.
- F_r: `F r = inverseImageIntegralModules l E (pointPower D r).hom`, the sectionwise
  pushforward along `proEtaleIsoPostcompose` with the completed coefficient map inverted.
  G_r: `pull D l E r`. Its complex version is `Gc`.
- j_r: `inverseImageFiniteComparisonComplex` (an iso, by `finiteComparison_isIso`).
- Γ_•: `sections`/`complexSections`/`derivedSections` of the descent node.
- u_r and I_r: `u` and `I` are the recorded `chainTransport` and `derivedTransport`.
  `derivedTransport` is the `.choose` of `point_system_transport_descent`, so that
  theorem stmt_dep is genuine. Each map is followed only by the termwise identity
  `mapHomologicalComplexCompIso (Iso.refl _)` or by Mathlib's `mapDerivedCategoryCompIso`.
- d_m and t_m: `Compositors.d`/`.t` are pinned by `HasSiteSections`/`HasSystemSections`.
  Each is the identity on every section x of M(h^m·(h·V)), read in M(h^{m+1}·V). These two
  site objects are Over objects with propositionally equal structure maps (h commutes
  with h^m), so the HEq is between propositionally equal types and is meaningful. It
  is not an HEq between merely isomorphic objects.
- The tensor reading of t_m ((x⊗1)⊗1 ↦ x⊗1): `Compositors.tensor` is pinned by
  `HasTensorUnits` on every section, since j_1∘F_1(j_m) and j_{m+1} are isomorphisms.
  This is the unit characterization of the canonical pullback composition (j is the
  adjunction unit x ↦ x⊗1). The dependency's `integralFiniteCanonicalPullbackComposition`
  is stated only at a single universe and at derived level, so it cannot be applied
  to t ≠ u.
- The coefficient transport U_s G_r = F_r U_s: `Compositors.b`, pinned by
  `HasRestrictionSections` as the identity on sections.
- The normalized Roos identification θ: `RoosNormalization`. `ordinary` is pinned by
  the limit projections. `unit` is pinned on K-injectives and extends to all towers by
  naturality along K-injective resolutions. `theta` is pinned through
  `theta_normalization`, because unit is invertible on K-injectives and both functors
  invert quasi-isomorphisms.
- φ (product comparison): `Comparisons.psi`, pinned by `HasProducts` on every projection.
- κ: `Comparisons.kappa`, pinned by `HasFirstCoordinate`/`HasSecondCoordinate` in every
  degree p+1 for p ∈ ℤ. `coordinates` is an isomorphism, the signed (x,y) of the node.
  The two right sides each read only one coordinate, so the off-diagonal entries vanish.
- a_r = θ^{-1}κF_r(θ): `Comparisons.a`, pinned by `HasDerivedModel` on every Q(M).
  Every object of D(S_s) is isomorphic to some Q(M), so with naturality this pins a.
  The orientation was rechecked: a ≫ θ_{GM} = F(θ_M) ≫ κ.

Every existential witness is therefore uniquely determined by its normalization
conjunct. The ∃ only packages the canonical maps; it gives no free choice.

Conclusion clauses (each for all m ≥ 1):

- u_{m+1,M} = Γ(t_{m,M})u_{1,G_mM}u_{m,M} as chain maps of entire towers:
  `StrictTransportCoherence`, quantified over every M, in diagrammatic order.
- I_{m+1,C} = Γ(t_{m,C})I_{1,G_mC}I_{m,C} for every C: `DerivedTransportCoherence`.
  `td` is Mathlib-canonical `mapDerivedCategoryCompNatIso (P.t m)`.
- The equality of product maps on both summands: `ProductCoherence` (node step 5) and
  `ConeCoherence` (step 6, the whole cone).
- a_{m+1,C}d_{m,N} = L_s(t_{m,C})a_{1,G_mC}F_1(a_{m,C}): `DerivedComparisonCoherence`.
  `dd` is `mapDerivedCategoryCompNatIso (P.d m)`, with source F_1F_m.

Edge cases: m = 1 (power 2) is included. r = 0 is never used by u or I. Zero systems,
complexes in a single degree and non-surjective transitions are all admitted. No
constructibility, boundedness or normalization of N is assumed.

Searches: the node and worker records contain all three kinds. At review, a repository
grep for the item's declaration and for a power/Roos compositor found no duplicate.

## Validation

The final single-file scompile.py check passed cleanly in sandbox mode (35.4 s) and
with the real library module name (31.3 s), each under the original 60-second limit.
There are no compiler errors or warnings. The node signature is copied verbatim
from the module, all 30 helper/main declarations are recorded, and the only node
field changes are lean and the addition of def-weil-strict-roos-model to stmt_deps.
