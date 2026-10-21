## Worker report

Item: `lem-sf-derived-immersion-comparison-normalization`, group Q38, 2026-10-21.
Module: `Sheaf.AlgebraicGeometry.DerivedImmersionComparisonNormalization`.
The delivery states the node without changing its mathematical statement or dependencies.
All five theorem bodies are `by sorry`. Every helper has actual data assembled from the
published canonical functors, adjunctions and localization compositors. There are no new
nodes or dependency repairs.

### Hypotheses and objects

- The finite discrete commutative coefficient ring is `(A : Type (u + 1)) [CommRing A]
  [Finite A]`. Discreteness means constant coefficients; it requires no topological ring
  structure. No nonzero-ring hypothesis is imposed.
- Schemes are `Scheme.{u}`. Their site morphisms retain universe `u` and objects retain
  universe `u + 1`; these universes have not been identified.
- Noetherian means `[IsLocallyNoetherian X] [CompactSpace X]`, exactly the two conditions
  in the node. These hypotheses occur on each theorem. The definitions do not need them
  except for the termwise closed direct-image descent, which uses the stated exactness.
- Open and closed immersions are `(j : U ⟶ X) [IsOpenImmersion j]` and `(h : Z ⟶ X)
  [IsClosedImmersion h]`. There is no extra quasi-compactness assumption on j or h.
- `D(T_e,A)` is `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`,
  the existing `Etale.DerivedCategoryModule` presentation. On the pro-etale side use
  `Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)` and its derived category.
  This is the already-published fixed-scalar presentation used by the recorded open
  comparison and closed mate. The dependency `ProEtaleFiniteModules` realizes these as
  modules over its continuous-function coefficient sheaf. The intrinsic constant-ring
  extension `Scheme.sfIntrinsicExtensionByZero` is itself the transport of this same
  `ProEtale.openImmersionLowerShriek` through `sfIntrinsicModuleEquivalence`; we use its
  existing middle functor, rather than define a competing extension.
- C_T is `(comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory`, and on D+
  it is `.mapDerivedCategoryPlus`, definitionally the recorded
  `siteComparisonDerivedPullbackPlus`. No choice of comparison functor is made.

### Each clause

1. `derivedImmersionOpenPullbackComparison` is a_j in localization-restriction form.
   It localizes `openComparisonRestrictionIso`, whose middle factor is precisely
   `supportSiteComparisonCoefficientPullbackIso`, conjugated by the canonical
   inverse-image/restriction identifications. The source and target are split using
   `Functor.mapDerivedCategoryCompIso`, in the order inverse source compositor,
   localized sheaf isomorphism, forward target compositor.
2. `derivedImmersionOpenExtensionComparison` is o_j, applying the same construction to
   the recorded `openImmersionLowerShriekComparisonUpperStarIso`. Its source is
   D(j_e,!) followed by C_X, and its target is C_U followed by D(j_p,!).
3. `derivedImmersionOpenEtaleAdjunction` and `derivedImmersionOpenProEtaleAdjunction`
   use the existing `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction` on
   the two ordinary open adjunctions. Their units and counits are the specified
   termwise localizations; no adjunction is selected by a mere existence theorem.
4. The first conjunct of `derivedImmersionOpen_normalization` is the first displayed
   open equation for every unbounded L. Lean composition is left to right: its factors
   are C_U(eta_e), a at j_e,!L, and j_p^*(o_L), in that order.
5. The second conjunct is the second displayed open equation for every unbounded M.
   Its factors are o at j_e^*M, j_p,!(a_M), and e_p at C_X M. Its right-hand side is
   exactly C_X(e_e at M).
6. The last conjunct states that the etale unit at L and the pro-etale unit at C_U L
   are invertible. Together with the first equation this states the node's open
   restriction identity: eta_p^{-1} after j_p^*(o_L) after a after C_U(eta_e) is the
   identity of C_U L. This is the displayed unit equation with the invertible target
   unit cancelled, not an additional arbitrary normalization.
7. `derivedImmersionClosedEtale_exact` and `derivedImmersionClosedProEtale_exact`
   give `PreservesFiniteColimits` of the two ordinary closed direct images. Both
   already preserve limits as the existing right adjoints, so these are precisely
   exactness, not a one-sided weakened condition. They are registered as named proof
   instances so the subsequent exact derived functors can be typed. Their data is
   a proposition; no object is chosen from an undetermined existence assertion.
8. `derivedImmersionClosed_sheaf_transpose` identifies the existing actual ordinary
   map `lowerStarComparisonUpperStarBaseChange h ...` with the homEquiv transpose
   required for delta_h^0. The input is a_h^{-1} at h_e,*F, followed by C_Z(epsilon_e).
   The former is `(comparisonUpperStarCompUpperStarIso ... h).hom`, since a_h has the
   opposite orientation. This is an equality of specified morphisms, not existence
   of a map or an isomorphism with the same endpoints.
9. `derivedImmersionClosedTermwiseComparison` localizes this same ordinary mate,
   using `mapDerivedCategoryPlusNatIso` and the canonical plus compositors. Closed
   immersions are qcqs, and the published `isIso_lowerStarComparisonUpperStarBaseChange`
   supplies invertibility of this actual ordinary map. Using `asIso` retains its
   forward morphism exactly; it does not choose another comparison.
10. The first conjunct of `derivedImmersionClosed_normalization` is equality of the
    termwise descent with `fixedComparisonDirectImageMatePlus` under the canonical
    `rightDerivedFunctorPlusIsoMapDerivedCategoryPlus` identifications. Both sides
    start at C_X(Rh_e,* L) and finish at D(h_p,*)(C_Z L). The right side first maps
    Rh_e,* L to D(h_e,*)L, then uses the termwise delta. The left side first uses
    the named derived delta, then maps Rh_p,* to D(h_p,*).
11. Its second conjunct is the displayed closed counit equation for the same specified
    delta, with the recorded `fixedComparisonPullbackPlus` and the two recorded
    `derivedUpperStarLowerStarAdjunctionPlus` counits. It is restricted only to D+,
    as the node requires.
12. Its last two conjuncts say that both closed derived counits in this equation are
    invertible (the pro-etale one at C_Z L). Cancelling C_Z(epsilon_e) in that equation
    gives precisely the identity of C_Z L under the counit identifications. No
    constructibility assumption is introduced.
13. Identity and composition identifications are retained by construction, through the
    recorded support-site pullback comparison and the standard exact-functor
    compositors. The open comparison uses the canonical restriction conversion of
    the same pullback comparison; the closed comparison uses the recorded
    `fixedComparisonPullbackPlus`. They are not independent isomorphism parameters.

### Dependency declarations used

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the `Etale.DerivedCategoryModule`
  encoding; the abstract `DerivedCategory`, `.Plus` and `homologyFunctor` are Mathlib.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, `finiteCoefficientRealization`, and
  `finiteCoefficientComparison` explain the fixed/intrinsic presentation used by the
  existing comparison APIs. They are available through the public dependency chain.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison` and
  `Scheme.proEtaleSiteComparisonModules`, the geometric morphism underlying C_T.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus`, the same fixed-coefficient C_T on D+.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso` and its coherence theorem.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `Etale.openImmersionLowerShriek`, `.openImmersionLowerShriekAdjunction`, and
  `.openImmersionRestrictionLowerStarAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicExtensionByZero`, its fixed-scalar middle functor
  `ProEtale.openImmersionLowerShriek`, and `Scheme.sfIntrinsicModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparisonCoefficientPullbackIso` and
  `supportSiteComparison_pullback_coherent`.
- `Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization`:
  `openComparisonRestrictionIso` and `openComparison_unit_normalization`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonPullbackPlus`, `fixedComparisonDirectImageMatePlus`, and
  `fixedComparisonDirectImageMatePlus_counit`.
- `Sheaf.SixFunctors.OpenTensorNormalizationData`:
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact`:
  `Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus`.

The other already-stated proof prerequisites are imported without `public`.
For `lem-exc-proetale-closed-exact`, the old non-FiniteCoefficient module is the
incompatible legacy family. This delivery imports its existing upstream
`FiniteCoefficient.UpperLowerStar.ClosedImmersion` counterpart, containing the same
`ProEtale.preservesFiniteColimits_lowerStar_of_isCompl` statement and the recorded
fully-faithfulness declaration. It does not import both ownership families. The
Mathlib-only proof prerequisites have no project module to import.

### Edge cases and sources

Checked the empty scheme, empty open, empty closed subscheme, identity immersion,
zero sheaf/complex, zero coefficient ring, arbitrary negative lower bounds on D+,
and genuinely unbounded open inputs. No nonemptiness, characteristic, nontriviality,
constructibility or extra boundedness condition appears. The Noetherian target makes
the closed complement retrocompact, precisely the necessary pro-etale exactness
condition; this agrees with local Stacks `proetale.tex`, lemma
`closed-immersion-complement-retrocompact-exact` (09BM). Also read its
`closed-immersion` (09AA), `jshriek-comparison` (09AF), and `open-immersion` lemmas.
Read local `derived.tex`, `right-derived-exact-functor` (015F), and
`pre-derived-adjoint-functors-general` (0FND). Read the current blueprint source named
in the node, paragraph 2 of the finite-duality site-comparison proof. No statement
fault or disputed clause was found.

### Searches

- `msearch.py leanfinder`, query: "Derived etale proetale open extension comparison
  preserves units counits and closed direct image comparison is termwise sheaf mate".
  Eight generic sheaf-adjunction/whiskering hits; no statement of this node.
- `msearch.py loogle`, query:
  `CategoryTheory.Adjunction, CategoryTheory.Functor.mapDerivedCategory`.
  Zero hits; no exact match.
- `msearch.py leansearch`, query: "Canonical derived comparison of etale and proetale
  module sheaves commutes with open adjunction units counits and closed counit mates".
  Eight generic derived-adjunction and pushforward-adjunction hits; no site-comparison
  normalization statement.
- `msearch.py grep`, query `mapDerivedCategory.*[Cc]ounit|[Cc]omparison.*[Uu]nit`,
  in Mathlib `CategoryTheory`: 17 generic monad and sheaf-comparison hits; none exact.
- `rg` in Mathlib `CategoryTheory` and `Algebra/Homology` for
  `mapDerivedCategory.*[Cc]ounit|mapDerivedCategory.*[Uu]nit`: no matching statement.
- `rg` in `lean/WeilConjectures` for the item id: no match. In the finite-coefficient
  derived tree for comparison/unit/counit: related comparison and adjunction APIs,
  but not the open equations plus the closed exact-descent normalization.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for derived immersion comparison and immersion
  normalization: found `EtaleImmersionShriekNormalization`, which was read. It concerns
  the comparison with compactifications on the etale site, not this node's
  etale/pro-etale mate. `OpenComparisonUnitNormalization` states the ordinary sheaf
  unit equation and is used here, not copied. All proposed `derivedImmersionOpen*`
  and `derivedImmersionClosed*` declaration names were searched in both project roots;
  no prior owner was found.

### Validation

`scompile.py Q38 lem-sf-derived-immersion-comparison-normalization` compiled both the
sandbox and the actual module path cleanly (13.9 s and 12.3 s). No warning remains.
The initially absent colimit instances for restriction were supplied by exposing the
existing restriction/direct-image adjunctions as left-adjoint instances, with actual
proof terms and no new postponed theorem. Every theorem remains entirely `sorry`.

## Second reading by Q38

This is the author's second reading; the independent maintainer review follows delivery.
Reopened the JSON and Lean module and checked the two displayed open equations factor
by factor, including composition direction and the arguments of a and o. Both range over
the full unbounded derived categories. Checked that the open units come from localized
ordinary adjunctions, not just an isomorphic adjoint pair. Checked that delta^0 is the
existing ordinary comparison and that its transpose input uses the inverse of a, not a.
The first closed equality has the canonical Rh-to-D(h) comparisons on the correct sides;
the second has the named derived mate, not the termwise mate substituted in its place.
The invertibility clauses apply to exactly the counits in that equation. The restriction
identity clauses are their equations under these invertible identifications, so require
no choice of new maps. The fixed-scalar and intrinsic coefficient presentations are the
existing equivalent presentations already used by the recorded dependencies. No node
correction, dependency repair, additional mathematical hypothesis or omitted clause was
found. The only change after the first compile was the explicit exposure of the existing
restriction left-adjoint structures and the required proof imports.
