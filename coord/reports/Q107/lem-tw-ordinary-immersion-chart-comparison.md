## Worker report

The delivery states `WeilConjectures.OrdinaryImmersionChart.ordinaryImmersionChartComparison`
in `Sheaf.Paper.OrdinaryImmersionChartComparison`. Its only postponed theorem is that
main theorem, with proof `sorry`. All other declarations are abbreviations, actual
constructions from existing APIs, or records specifying the output comparisons.
There are no new DAG nodes, dependency repairs, or statement corrections.

Hypotheses and clauses, compared with the node:

- A prime ell is `l : ℕ` with `[Fact l.Prime]`. The finite extension is `E : Type u`
  with `[Field E]`, `[Algebra ℚ_[l] E]`, and `[FiniteDimensional ℚ_[l] E]`.
  The recorded `Padic.coefficientExtensionIntegers`, chosen uniformizer and actual
  quotients are used through `completedIntegralCommRingSheafUnrestricted`.
- Every scheme is `Scheme.{t}`. Its site is `Scheme.ProEt` with `ProEt.topology`;
  it keeps object universe t+1 and Hom universe t. Coefficients and modules live
  in `max u (t+1)`, so no equality of the scheme and coefficient universes is assumed.
  Positive level n is encoded by n+1, as in the existing coefficient tower.
- `Rings` forgets commutativity of the actual completed ring sheaf; `Modules`
  is the recorded `ringedSiteModules` abbreviation for `SheafOfModules`.
  `DerivedCategory (Modules l E T)` is the ordinary unbounded derived category,
  using the standard localization instance exported by the model module.
- For any g, `directRingMap` is the adjunct of `completedRingMap l E g` under
  `completedRingAdj`. The latter is the unique map with precisely the finite
  projection equations in the question. No arbitrary structural map is input.
- `push` is sectionwise Mathlib module direct image with that scalar action;
  `pull` is Mathlib's sheafified module pullback, its left adjoint. The existing
  `module_pushforward_isRightAdjoint_of_universes` supplies its universal property.
  This is ordinary tensor pullback, before completion. `adj` is its specified
  `pullbackPushforwardAdjunction`, rather than an arbitrary adjunction.
- `Image` packages P_g and epsilon on actual cochain complexes: `universal`
  is `IsLeftDerivedFunctor` at quasi-isomorphisms, and `computes` makes epsilon
  invertible on flat-term K-flat complexes (`Good`). This is the cochain-category
  localization version of the node's equivalent homotopy-category formulation.
  Existence of every Image is a conclusion, never an added hypothesis.
- The morphisms f and i are explicit binders, with only `[IsImmersion i]`.
  Mathlib `isImmersion_iff_exists` identifies this exactly with a closed immersion
  followed by an open immersion. X_S is `pullback f i`, j is `pullback.fst f i`,
  and f_S is `pullback.snd f i`. Their equality is `pullback.condition`.
- U is `U : S.ProEt`; V is `(proEtaleBaseChange f_S).obj U`, whose underlying
  scheme is `pullback U.hom f_S`. The node's X_S times_S U is canonically the
  same fibre product with factors interchanged. The map v is the actual projection
  `completedRingSliceArrow f_S U = pullback.fst U.hom f_S`.
- `ImmersionSquare.comparison` is `Pf.functor ⋙ Pj.functor ≅ Pi.functor ⋙ Ps.functor`:
  at K this is exactly j* P_f K ≅ P_fS (i* K). Its limits/colimits fields assert
  exactness of i* and j*; `iExact` and `jExact` make their computation counits
  invertible on every complex, identifying these derived functors with ordinary
  exact immersion restrictions, without requiring derived completeness.
- `Square` fixes the underlying ordinary comparison by `squareSiteIso`, the
  actual fibre-product compositors and transport across the equality of scheme
  composites. `sections` fixes direct image on every section, and `mate` fixes
  ordinary pullback as its adjunction mate. `ImmersionSquare.normalization` then
  fixes the derived comparison via the two epsilon maps on each `Good` complex.
  This characterizes the composition comparison requested in the node.
- `chartRingIso` takes the existing slice/coefficient identification from
  `completedRingMap_slice` for the identity morphism. That theorem fixes it by
  identity-on-constants finite comparisons and every completed projection.
  These equations uniquely determine the ring isomorphism, so the selection is
  from a universal characterization, not arbitrary data from a mere existence.
- `restrict` is sectionwise restriction along the localization functor
  `MorphismProperty.Over.map ⊤ U.prop`, with scalars transported by that very
  coefficient isomorphism. The recorded `ProEt.sliceDense` equivalence identifies
  it with restriction on the localized site. `Chart.uLimits/uColimits` and
  `vLimits/vColimits` assert exactness. `Chart.rU/rV : ExactImage` retain the
  natural isomorphisms with termwise restriction on every complex.
- `setPull`, `setAdj`, and `representableIso` use the actual sheafified Kan
  inverse image and `Adjunction.uliftYonedaCompIso`: this is f_S^-1 h_U ≅ h_V,
  whose adjunct is normalized at id_U by the recorded representable theorem.
- `Chart.direct.sections` is normalized by `completedRingSlicePointIso`, namely
  the actual isomorphism H times_U V ≅ H times_S X_S. These are module morphisms
  with the scalar actions from `directRingMap` and `chartRingIso`; hence the
  comparison identifies ringed morphisms, including c_v, rather than just topoi.
  `Chart.ordinary` is its inverse-image mate, fixed explicitly by unit,
  direct-image comparison, and counit in `Chart.mate`.
- `Chart.comparison` is theta: r_U followed by P_v ≅ P_fS followed by r_V.
  Its `normalization` equation identifies theta with the ordinary comparison
  on every flat-term K-flat representative, with the original epsilon maps.
- `Comparison.comparison` gives the second natural isomorphism
  (P_f followed by j*) followed by r_V ≅ (i* followed by r_U) followed by P_v.
  `Comparison.formula` is literally restriction of the first isomorphism,
  followed by the inverse of `Chart.comparison`, with functor associators.
- Both are natural isomorphisms of functors on the entire ordinary derived
  category, so they apply naturally to every K, including unbounded K.
  No noetherianity, completeness, boundedness, separatedness, field, or flatness
  condition on any structural map occurs among the theorem's hypotheses.

Dependency declarations read and used (including imports reserved for stage 3):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public
  `CoefficientExtension`: `Padic.coefficientExtensionRing`, its valuation ring,
  uniformizer, transition maps, and `finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`;
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`, its
  continuity and finite limits, inverse image and its actual adjunction.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its public imports:
  `completedIntegralCommRingSheafUnrestricted`, its finite projections and tower.
- `Sheaf.Paper.CompletedCoefficientRingedCoherence`: `completedRingMap`,
  `completedRingAdj`, `completedRingComp`, `completedRingMap_equal_composites`,
  `completedRingRestriction`, `completedRingMap_slice`, and slice-point maps.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and Q;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: existing
  sheaf tensor and its independent-universe monoidal structures.
- Mathlib `IsClosedImmersion`, `IsOpenImmersion`, and `IsImmersion`, with
  `isImmersion_iff_exists` and its base-change instances. The convention node
  `def-weil-scheme-morphism-properties` has no separate declaration to import.
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`:
  `SheafOfModules.ringedTopoiDerivedPullbackIndependent`; the universal counit
  and K-flat computation clauses are retained in `Image`.
- `Sheaf.Paper.SfImmersionCompletedPullbackComparison`:
  `Scheme.ImmersionCompletedPullback.immersion_completed_pullback_comparison`
  and its ordinary exact-restriction clauses; the complete-object clauses are
  not assumptions here. The new signature retains independent universes.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.pushforward`, `overFunctor`, `overMap`, `overFunctorMap`.
  Restriction is expressed directly on schemes via the recorded slice equivalence.
- `Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback`:
  `siteRepresentableAlgebraicPullback` and `Adjunction.uliftYonedaCompIso`;
  `Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`:
  `exists_localizedSheavesOverRepresentable_general`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `integralTowerGeneralPullbackComposition`; `Sheaf.Paper.SheafSliceDerivedComparison`:
  `ringedSheafSliceDerivedComparison`, including its representative equations.
- Proof imports also retain `StandardQuotientsPerfect`,
  `ProfiniteCoefficientInverseImage`, `ProEtaleConstantRingOperations`, and
  `KFlatResolutionIndependentCoefficients`, as required by the DAG proof plan.
- `lem-tw-representable-slice-localized-ringed-morphism` is a proof dependency
  with no recorded Lean declaration in the read clone, so there is no module
  to import for it yet. No object used in this statement waits on that proof:
  the sectionwise ringed slice comparison is specified in `Chart` itself.

Additional existing APIs: `CompletedCoefficientPushforward.ExactImage` provides
exact derived restriction data, `CompletedCoefficientPushforward.modAbelian` and
`hasDerived` supply the existing structures, `PullbackExistsOfUniverses` supplies
module adjoints, and `SubterminalImageCalculus.pushforwardAdditive` supplies
additivity. The wrappers and output records belong to this node's comparison;
they introduce no second mathematical module category, ring, tensor, or pullback.

Edge cases checked: i=id, f=id, U the final represented object, U empty, X or S
empty, the zero complex, and arbitrary unbounded complexes are all admitted.
Positive levels start at 1 via n+1, so exponent zero is not accidentally used as
one of the nonzero levels. There is no nonemptiness assumption on a scheme or
chart. No characteristic or base-field exclusion is imposed. Universe t and u
are independent throughout. The flat-term restriction occurs only in the
normalization clause, while the two comparisons apply to every derived object.

Searches (the actual persisted `searches.jsonl` records were inspected after the
interruption; no search result is invented):

- Loogle, `"SheafOfModules.pullbackComp"`: `PresheafOfModules.pullbackComp` and
  `SheafOfModules.pullbackComp`; these only state ordinary composition.
- Mathlib grep, `pullbackComp|restrictFunctorIsoPullback`, subdirectory
  `Algebra/Category/ModuleCat`: ordinary sheaf/presheaf composition declarations.
- LeanFinder, `Ordinary derived pullback on pro-etale sheaves commutes with
  immersion restriction and representable chart localization`: Zariski
  `Scheme.Modules.restrictFunctorIsoPullback`, `restrictFunctorComp`, and
  open-immersion pullback lemmas; no exact statement.
- LeanSearch, `Derived pullback of module sheaves commutes with restriction to a
  representable slice and a locally closed immersion`: ordinary pullback and
  adjunction APIs and Zariski restriction; no exact unbounded pro-etale statement.
- `rg` of the item id and `OrdinaryImmersionChart|ordinaryImmersionChartComparison`
  in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`:
  no existing declaration. Concept searches located the dependency composition,
  ringed-slice and completed-coefficient interfaces used above.

Source checked: local `sites-cohomology.tex`, lemma-derived-pullback-composition
(Tag 0D6D), and `sites-modules.tex`, lemma-localize-morphism-ringed-topoi (04IF).
The former computes composition on flat-term K-flat representatives; the latter
fixes the localized inverse image and structural map by the actual ringed square.
The node's four proof steps are transcribed into the main theorem's docstring.
No STATEMENT-DISPUTED issue was found.

Validation: prescribed `scompile.py Q107 lem-tw-ordinary-immersion-chart-comparison`
on the delivered module completed with exit code 0, both as sandbox and as its
actual library name (35.9 s and 43.6 s), with no errors or non-sorry warnings.

## Second reading by Q107

A separate second pass by the same dispatched worker (the dispatch explicitly
forbids starting other agents) compared the original node and the compiled file.
It checked the hypotheses and every clause listed above. In particular, the
orientation of theta is r_U P_v to P_fS r_V, its inverse occurs in the final
formula, and the square uses the correct fst and snd projections. The output
records assert actual natural isomorphisms, not pointwise mere isomorphism
classes, and their section and counit equations fix the canonical maps.
`Image` is ordinary derived pullback, and `iExact/jExact` extend over all complexes;
no completeness restriction is hidden there. Scalar actions are the adjuncts of
the existing projection-defined c_g maps. The standard derived-category instance
and independent coefficient universe introduce no mathematical hypothesis.
The only selected auxiliary ring data is uniquely characterized by the constant
and finite-projection equations. No mismatch or correction was found in this pass.
The maintainer's independent review remains the independent reading of this delivery.
