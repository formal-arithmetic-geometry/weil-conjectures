## Worker report

The module `Sheaf.Paper.RealizationCompletedPull` states
`WeilConjectures.realization_completed_pull`. Its conclusion is the existential specification
`RealizationCompletedPullData` of a system for all of the schemes and morphisms in the
node. There is one postponed theorem, with `sorry`, and its docstring follows all
eight steps of the DAG proof. All helper definitions have real data. The arrow specification and existential predicate
are specifications of this node's comparisons, not independent coefficient,
completion, derived-category, or localization definitions. No new node and no
dependency repair is required. The item's statement and dependencies are unchanged.

Hypotheses and objects, matched to Lean:

| Node | Lean |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` |
| Finite normed extension E/Q_l | `[NormedField E] [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` |
| Valuation ring, fixed uniformizer and positive quotient levels | The existing `PbcIntegralRing l E`, `pbcUniformizer l E`, and `pbcIntegralDatum l E`; the size lift changes no ring, and index n denotes exponent n+1. |
| Field k of positive prime characteristic different from ell | `[Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]` |
| Schemes separated and finite type over k | `RealizationPullScheme.over`, `.finiteType`, `.quasiCompact`, `.separated`; finite type is locally finite type plus quasi-compactness. |
| Explicit Noetherian, finite dimension, local invertibility | `.noetherian`, `.dimension`, `.invertible` on each bundled scheme |
| Every k-morphism h, and further k-morphism j | `RealizationPullHom T U` is exactly the Hom in the scheme over-category; `.left` is the actual scheme morphism, with its over-k equation retained. |
| Small pro-etale site, integral limit coefficients A_T | `ProEt.topology T.scheme`, `pbcAdicCompletion T.scheme (pbcIntegralDatum l E)`; site and coefficient universes are those of the published definitions. |
| Continuous E-valued functions and their integral algebra | The existing `RealizationScalarFunctorData` supplies `integralIso`, its finite-quotient normalization, and `inclusion` with pointwise inclusion normalization; `realizationPullScalarMap` is exactly their composite. |
| Integral full subcategory I_T | `PbcBoundedConstructibleComplete` and its existing predicate, with all completeness, uniform-tower and compatible-origin conditions retained |
| Raw rationalization R_T and F_T | `PbcRationalCategory` and `pbcDerivedExtend (realizationPullScalarMap ...)`; `realizationPullRationalScalar` is the published J followed by the published section-module encoding. `realizationPullIntegral` is exactly the published `s.integral`, with the named scalar map unfolded. |

Conclusions and normalizations, clause by clause:

1. `RealizationCompletedPullArrow.coefficient_isIso` concerns the actual
   `completedCoefficientMap`, not a replacement map. That published definition
   is `limit.lift` of `completedCoefficientComponent`: inverse image of the
   finite projection followed by `completedFiniteCoefficientMap`. These are the
   finite constant-section maps, so the finite-projection characterization is
   precisely the canonical profinite comparison in the dependency.
   `coefficient_normalization` transports this very map through the two
   `integralIso`s and asserts precomposition with the first fiber-product
   projection via `integralCoefficientRestrictionNormalized`.
2. `ordinary_mem` asserts that the actual ordinary derived module pullback of
   each integral object is integral. `completed_mem` gives the actual strict
   quotient-tower object its full integral membership. `unit_isIso` asserts
   invertibility of `pbcActualStrictCompletedPullUnit` at that same object. This
   unit is the published constant-tower adjunction unit followed by derived
   limit of the strict quotient augmentation; no cone-map replacement occurs.
3. `rationalCoefficient`, `rational_normalization`, and `coefficient_square`
   specify the actual rational coefficient identification by precomposition
   and the localization-unit square with the actual integral coefficient map.
   `continuousPull` is `proEtaleRingDerivedPullback` for that identification.
   These are sectionwise coordinates for the continuous coefficient modules
   of the recorded condensed-module encoding; neither a discrete E sheaf nor
   a new module category is introduced.
4. `moduleComparison` and `module_unit` specify the ordinary scalar/pullback
   comparison on the two actual tensor units. This is the unit normalization
   of `existsUnique_localizationInverseImage`, in the direction inverse to its
   beta. `module_fraction` states the same formula with the coefficient
   `1/varpi^n` on both sides, for every chart, numerator section and n. The
   helper `realizationPullDenominator` is a constant continuous E-valued
   function. Arbitrary local sections and restriction/sheafification give the
   sheaf-local fraction meaning; no global denominator assumption is made.
5. `complexComparison`, `complex_terms`, and `derived_normalization` fix the
   unbounded comparison on actual representatives using the published scalar
   and ordinary-pullback counits and the exact continuous-pullback factors.
   They retain the actual termwise comparison. `ordinaryComparison` is
   therefore not an unspecified isomorphism between the functors.
6. `alpha` has source F_T C_h and target Q_h F_U on the full integral
   subcategory. `alpha_normalization` says `F_T(gamma_h) ≫ alpha_h = B_h`.
   Since `unit_isIso` asserts precisely that gamma_h is invertible, this is
   exactly `alpha_h = F_T(gamma_h^{-1}) ≫ B_h`, with the node's order of
   factors. Together with `module_unit` it preserves localization units after
   the specified completion identification, and `module_fraction` retains
   the denominator.
7. `coefficient_comp` fixes the composite rational coefficient identification.
   `rationalComp_canonical` identifies `rationalComp` with the inverse of
   `integralTowerGeneralPullbackComposition`, including its representative
   normalization. HEq only transports along the propositional coefficient
   equality; it does not permit an arbitrary comparison.
8. `completedComp_normalization` is the node's defining equation for q,
   written in Lean's left-to-right composition order, using the inverse of
   `pbcActualDerivedPullCompIso` for p. `completedComp_unique` quantifies over
   every competing component isomorphism and asserts equality. The field
   `completedComp` itself is a natural isomorphism, retaining naturality in K.
9. `alpha_comp` is exactly the node's completed scalar composition equation.
   Its inner argument is `integralCompleted.obj K`, whose underlying object
   is the actual C_j(K), with the membership proof of clause 2.
10. `moduleId_unit` characterizes the ordinary E-coefficient identity comparison
    on the actual inverse-image unit and first projection of identity base
    change. `continuousId_normalization` descends that exact identity to all
    complexes. `alpha_id` is the node's identity equation precomposed with
    invertible F_T(gamma_id); cancelling this factor gives the equation as
    written in the node. Thus the completed identity is gamma_id inverse
    followed by the ordinary identity, rather than a separately chosen map.
11. `integralOrdinary`/`integralCompleted` use `pbcConditionalIntegral` of the
    actual ambient functors. Their linearity fields are conclusions, not new
    assumptions of the theorem. `rationalOrdinary`/`rationalCompleted` apply
    the existing `ScalarLocalization.transport` to those exact restrictions.
    `rawFractions` writes the image of f/varpi^n explicitly, with the same
    denominator for ordinary and completed pullback.
12. `rationalAlpha_integral` fixes the extension of alpha on every integral
    object using the scalar functor's actual integral comparison.
    `rawUnit_integral`, `rawComp_integral`, and `rawId_integral` likewise fix
    the raw rationalized unit, composition, and identity components to the
    rationalization of the specified integral arrows. `rawAlpha_comp` and
    `rawAlpha_id` state the corresponding equations on every raw rational
    object. Objects remain integral objects with localized Hom modules.
13. There is no cartesian-square, properness, flatness of h, nonempty-scheme,
    lattice choice, Karoubi envelope, or additional universe equality binder.

Dependency declarations used (including public reexports of the records):

- `Sheaf.Paper.IntegralUniformCoefficient`: the recorded specialization
  `pbcBoundedConstructibleComplete`; its reexported
  `PbcBoundedConstructibleComplete`, `PbcIsBoundedConstructibleComplete`,
  `PbcIntegralRing`, `pbcIntegralDatum`, and `pbcUniformizer` are the precise
  coefficient-sized specialization also used by the scalar-functor dependency.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`,
  `pbcRationalization`, and the canonical integral A-linear structures.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`: the recorded
  `Profinite.isCommMonObj_continuousCoefficientRingObj` and its reexported
  continuous ring objects, archived bounded constructible category, and
  actual module operations.
- `Sheaf.Paper.RealizationScalarFunctor`:
  `WeilConjectures.RealizationScalarFunctorData` and
  `WeilConjectures.realization_scalar_functor`, including coefficient,
  scalar-unit, fraction, and integral comparison fields.
- `Sheaf.Paper.PbcQbarCompletedPullback`: the recorded dependency's public
  reexports `pbcActualStrictCompletedPull`,
  `pbcActualStrictCompletedPullUnit`, `completedCoefficientMap`,
  `pbcActualDerivedPull`, `pbcActualPullComplexCounit`, and the normalized
  `pbcActualDerivedPullCompIso`/`pbcActualDerivedPullIdIso` interfaces.
  The Qbar-specific functor is not used as the finite-E pullback.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the recorded
  constant-ring operations and their general reexports
  `proEtaleRingModulePullback`, `proEtaleRingDerivedPullback`, and
  `proEtaleRingDerivedPullbackFactors`.
- `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`:
  `existsUnique_localizationInverseImage`,
  `existsUnique_localizationInverseImageRing`,
  `localizationInverseImage_fraction`, `_comp`, `_id`,
  `localizationComparisonDerived`, and its unit/coherence equations form
  the proof's exact localization-comparison interface.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`:
  `continuousCoefficientImmersionRestriction` and its reexported
  `integralCoefficientRestrictionNormalized`,
  `rationalCoefficientRestrictionNormalized`, integral/rational coefficient
  sheaves, and coefficient-value conventions. Its immersion-only comparison
  is not incorrectly applied to arbitrary h: this node asserts the general
  comparison of the actual completed coefficient map instead.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and the actual recorded valuation
  ring/uniformizer constructions.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`:
  `proEtale_profinite_coefficient_inverse_image` and its canonical
  finite-projection and identity/composition comparisons.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `WeilConjectures.integralTowerGeneralPullbackComposition`, the direct
  alias of the full general `proEtaleCanonicalPullbackComposition`; also
  `proEtaleRingModuleUnitSection` from the reexported general interface.

Proof imports include every recorded stated proof dependency. The Mathlib
leaves use `Precoverage.mem_coverings_of_isPullback` with the fpqc stability
instance, `MorphismProperty.comp_mem`/`pullback_fst` for WeaklyEtale, and
`Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField`.

Sources read: the target node and every statement-dependency record, the full
signatures/docstrings of the interfaces above, the current blueprint finite
extension proof, and the local Bhatt--Scholze PDF converted to text, especially
Proposition 6.6.11 (stratified perfect local models), Lemma 6.8.2 (localization),
and Remark 6.8.15 (ordinary inverse image with continuous coefficients).

Searches actually run via msearch.py:

- LeanFinder: `Derived completion unit pullback constructible integral l-adic
  complexes commutes with scalar extension`: eight hits on algebraic adic
  completion, BDeRhamPlus and lift formulas; no exact comparison theorem.
- Loogle: `Functor.mapIso, CategoryTheory.NatIso`: no hits; tool reported
  unknown identifier `Functor.mapIso`.
- Mathlib grep: `completedPullback|completedUpperStar|completionUnit`: no hits.
- LeanSearch: `scalar extension derived completion pullback constructible
  l-adic complexes`: eight hits on algebraic AdicCompletion instances and
  PresheafOfModules.pullback; no exact comparison.
- rg of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for the item id and proposed declaration names: no existing exact theorem
  or name collision. Related strict-pullback, ordinary scalar comparison,
  and finite-extension scalar-comparison interfaces were inspected and reused;
  none states rational realization of strict completed pullback with all of
  this node's unit and coherence normalizations.

Edge cases checked before and during writing: empty schemes are permitted by
all record fields; no point or nonzero global section is selected. The zero
complex is included in both full subcategories and all naturality equations.
For n=0 the denominator is 1 and the fraction formula is the unit formula;
quotient-tower n=0 is separately the positive first quotient. Identity and
composable arbitrary morphisms are explicit, with no immersion or properness
restriction. Ramified extensions retain the chosen uniformizer, rather than
replacing it with ell. Finite-type schemes need not be smooth, connected,
nonempty, affine, or proper. Site object/morphism and coefficient universes
are the published ones, including ULift of the integral ring.

No STATEMENT-DISPUTED and no source-based statement correction.

## Second reading by NC

Author's second pass against the node and the finished declarations; the
dispatcher forbids starting another agent and reserves independent review to
the maintainer. I checked the source and target of each comparison, Lean's
left-to-right composition order, the actual strict-tower unit, uniqueness of
the completed comparison, and the ordinary E identity/composition normalization.
The checks found and repaired an opaque scalar-map presentation mismatch in
`s.integral`; `realizationPullIntegral` now exposes exactly that same map.
They also moved A-linearity to the actual integral restrictions used by raw
rationalization and made identity base-change properties explicit. No
mathematical statement or hypothesis changed. The table and numbered clauses
above are the complete hypothesis/clause audit.

The helper `realizationPullSiteId` is the existing
`MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T`, exposed with the explicit
site-functor type. It constructs no replacement site comparison and adds no
hypothesis. The alias keeps identity-normalization elaboration from choosing
an incompatible category instance while inferring the properties.

`RealizationCompletedPullData` uses existential data families and conjunctions
of the fifteen `realizationPullLaw...` predicates. Those predicates state the
clauses named above, separately, to avoid repeatedly elaborating one enormous
dependent expression. The final theorem asserts their conjunction for the
same coherent system. There is no extra premise in these predicates.

`RealizationCompletedPullArrow` extends two smaller records:
`RealizationCompletedPullCoefficients` contains the five coefficient clauses,
and `RealizationCompletedPullIntegral` contains the seven integral membership,
unit and linearity clauses. The nine remaining fields specify the scalar
comparison. All twenty-one original components remain available by projection.
This decomposition changes only the Lean presentation.

`realizationPullRawFraction` names `(1/varpi)^n` acting on the image of f under
the actual rationalization functor. The two `rawFractions` equations use this
expression with exactly the same n. It is the same pure tensor
`(1/varpi)^n ⊗ f`, expressed using the existing localization action, and retains
the actual numerator and denominator.

Validation: `scompile.py NC lem-weil-pbc-realization-completed-pull` compiled
the complete delivered file, both in its sandbox namespace (39.7 seconds)
and as `Sheaf.Paper.RealizationCompletedPull` (55.6 seconds), under the standard
60-second limit. Both checks were clean, with no warnings. The final auxiliary
names were also searched in Mathlib, WeilConjectures and Sheaf; no collision was
found. Only the node's `lean` field changes, and its primary signature is copied
verbatim from the delivered theorem.
