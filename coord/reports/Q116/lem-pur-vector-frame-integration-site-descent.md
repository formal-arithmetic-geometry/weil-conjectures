## Worker report

The module `Sheaf.Paper.VectorFrameIntegrationSiteDescent` states the finite-field frame-action descent theorem as `AlgebraicGeometry.ProEtale.VectorIntegrationSite.finiteTypeVectorFrameIntegrationSiteDescent`. Its conclusion is the fully defined proposition `FiniteTypeFrameDescent`. The auxiliary Noetherian-base descent and frame-action theorems state the two components separately. Each of the three theorem proofs is `sorry`; every definition has complete data. These helper declarations express this node's own objects, maps and clauses, not a new independent notion.

The source read was the whole current blueprint proof `main-20261015/blueprint/sec-smooth-purity/sk-prop-an/def-amb-vector-integration.proof.md`: concentration on a frame cover and overlap equality by linear trace invariance. The expanded seven-step DAG proof specifies the two-site exchanges. The degree-zero ingredients were checked against Stacks `derived.tex`, Tag 06XS, `lemma-negative-exts`; `sites-modules.tex`, Tag 03EM, `lemma-internal-hom`; and `sites.tex`, Tag 04TQ, `lemma-glue-maps`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Finite-field/coefficient conventions; positive quotient level | `P : WeilConjectures.PurityFiniteSetting`, including `P.level_pos`; the existing ring `Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)` is the standard size lift of the quotient at level `(P.level - 1) + 1 = P.level`. |
| Finite-type scheme over k, with no separatedness of S | `T`, `aT : T ⟶ Spec (CommRingCat.of P.field.k)`, `[LocallyOfFiniteType aT] [QuasiCompact aT]`. There is no separatedness binder. `FiniteTypeFrameDescent` installs the implied Noetherian instance. |
| Ell invertible on every open | `∃ hT : IsUnit (P.coefficients.l : Γ(T, ⊤))` is a conclusion from the finite-field data, not an extra assumption; its images give the open witnesses. |
| Choose r ≥ 1 annihilating A | `∀ s : ℕ, ∀ hB : (ell^(s+1) : A) = 0`; this is exactly `r'=r-1` from the node. No divisibility by the ramification index is imposed. |
| Fixed ordinary constant-A small-site derived categories | All sources and targets use `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u+1} A))` or `DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u+1} A))`. The pro-etale object/morphism universe distinction is retained. |
| Comparison and root-normalized Tate tensor inputs | Existing `comparison`, `Etale.vectorIntegrationCoefficient`, `affineTraceRight`, `pullback` and `pullbackUnit` are reused. The source on the pro-etale side is written in the specified root-comparison coordinates `C(K^e)`, canonically `A_V(d)[2d]`, as in the recorded frame/vector integration definitions. The existing coefficient is the d-fold shifted derived tensor, including its zero-fold unit. |
| Projective completion of the rank-d vector bundle | `rank : ℕ`, `M : T.Modules`, `[M.IsFiniteLocallyFreeOfRank rank]`; quantify over `c : Compactification (VectorBundleZeroSection.π T rank M)` satisfying `IsFrameDescentProjectiveCompletion`. This predicate uses the existing `VectorProjectiveCompletion.Presentation`, dehomogenization maps with their generator/scalar formulas, equality of the proper object with its relative Proj, its projection, its standard open image and its prescribed affine charts. No completion is selected from an uncharacterized existence statement. |
| The prescribed Fe, Fp and comparison B | `frameDescentEtaleSource`, `frameDescentProSource`, and `frameDescentSite`. The latter is literally `compactSupportSiteComparison.app` on the bounded-below Tate input; its inverse has the node's B orientation. It is the actual proper-counit-mate and adjoint-open composite. |
| Ordered pro-etale coordinate traces on every open are isomorphisms, compatible and compared | `FrameDescentTraceHypothesis` quantifies every open U, asserts `IsIso (orderedIntegration ...)` and equality to comparison of `frameDescentOrdinaryTrace`. The definition of ordered integration already expresses its source via the specified tower B. Thus the equality is `t_p B = C(t_e)` in those source coordinates. Open compatibility follows from this equality, ordinary trace restriction and canonical comparison coherence; no arbitrary family of trace maps is substituted. |
| Refinement, composition and open identities for B | The comparison is the exact canonical construction covered by the recorded `compactSupportSiteCoherence`, which is already available for this datum. The maps use those canonical changes. This is a known hypothesis for this fixed B, so no arbitrary comparison or additional structure is assumed. |
| Finite trivializing open cover, including an empty index type | `∀ (J : Type v) [Finite J] (U : J → T.Opens) (_hU : iSup U = ⊤) (e : ∀ j, Trivialization ... (U j))`. No inhabitance binder occurs. |
| Actual local maps from restriction and inverse-frame exchanges, then traces | `frameDescentLocal` uses the existing `localIntegration`, its actual trace-free coordinate prefix, the actual compactification/source comparison, and canonical restriction/unit identifications. `frameDescentEtaleChange` supplies ordinary compactification coordinates for the prescribed ordinary global trace. |
| GL action [x0:x] ↦ [x0:Gx] intertwines B | The second conjunct of `FiniteTypeFrameDescent` quantifies every open W (hence every overlap), compactification and `G : Matrix.GeneralLinearGroup (Fin rank) Γ(W.toScheme, ⊤)`, and asserts `FrameActionIntertwining`. `frameActionEtale` and `frameActionPro` are built from their respective actual compact-support base-change maps along `affineTraceLinearMap`, identity pullback, canonical Tate pullback and compactification change. The pro exchange is independently constructed. The normalized compactification change is the canonical comparison on both boundaries with ordinary common refinement in between; it contains no trace. The equation is `B ≫ rho_p = C(rho_e) ≫ B`. The projective extension realizes these same maps as explained in the proof docstring. |
| Local pro-etale maps agree on overlaps without affineness | First conjunct of `FrameDescentConclusion`, using `DegreeZeroMapGluing.onSmallerOpen` on `U i ⊓ U j` and the actual `upperStarComp`. |
| Me, Mp, C(Me) canonically H0[0] | Three `FrameDescentDegreeZero` conjuncts: `homologyConcentratedIn 0 0` and a unique isomorphism to `singleFunctor ... 0` of H0, characterized by identity on H0 through the canonical single/homology comparison. These are derived identifications, not only a cohomology-by-cohomology assertion. |
| Unique global morphism with these restrictions | `∃! t, ∀ i, upperStar.mapDerivedCategory.map t = frameDescentLocal ...`. |
| It is the named global pro-etale integration | `frameDescentGlobal` is the existing `vectorIntegration`, transported from its recorded canonical compactification by `frameDescentProChange`. Its all-frame restriction equation places this very named map among the unique glued maps. |
| Isomorphism and independence of cover and frames | `IsIso (frameDescentGlobal ...)`, and its restriction equation for every open W and every frame there. Combined with uniqueness for each finite cover, this gives both independence assertions. |
| Global comparison with prescribed ordinary integration | Last conjunct of `FrameDescentConclusion`: `frameDescentSite.inv ≫ frameDescentGlobal = comparison.map (frameDescentEtaleChange.hom ≫ Etale.vectorBundleIntegration ...)`. This is exactly `t_p B = C(t_e)` in the projective-completion coordinates. |
| Degree-zero gluing only | Overlap restrictions and degree-zero normalized identifications use the recorded `DegreeZeroMapGluing` interface; no descent principle for arbitrary derived morphisms is asserted. |

Dependency declarations read and reused (the remaining imported dependency interfaces provide the named coefficient/category presentations):

- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `def-amb-vector-integration`: `Sheaf.AlgebraicGeometry.VectorBundleIntegration`, `AlgebraicGeometry.Etale.vectorBundleIntegration`.
- `def-asd-vector-bundle-zero-section`: `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`, `AlgebraicGeometry.VectorBundleZeroSection.scheme`.
- `def-coefficient-twists-detailed`: `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`, `WeilConjectures.sfQbarTwistingFunctor`.
- `def-compact-support-direct-image-detailed`: `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`, `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`.
- `def-sf-comparison-derived-pullback`: `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`, `AlgebraicGeometry.ProEtale.siteComparisonDerivedPullbackPlus`.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`, `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`.
- `def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, `AlgebraicGeometry.ProEtale.FiniteCoefficientModules`.
- `lem-amb-affine-space-top-trace`: `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`, `AlgebraicGeometry.Etale.exists_affineSpaceTopTrace`.
- `lem-amb-finite-tate-site-descent`: `Sheaf.Paper.FiniteTateSiteDescent`, `AlgebraicGeometry.Scheme.finite_tate_site_descent`.
- `lem-cbc-proetale-extension-zero-comparison`: `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`, `AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparison_coherence`.
- `lem-pur-compact-support-site-coherence`: `Sheaf.Paper.CompactSupportSiteCoherence`, `AlgebraicGeometry.ProEtale.compactSupportSiteCoherence`.
- `lem-pur-degree-zero-derived-map-gluing`: `Sheaf.Paper.DegreeZeroDerivedMapGluing`, `AlgebraicGeometry.DegreeZeroMapGluing.degreeZeroDerivedMapGluing`.
- `lem-weil-pbc-comparison-direct-image-canonical-mate`: `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`, `AlgebraicGeometry.ProEtale.fixedComparisonDirectImageMatePlus`.
- `def-sf-compact-support-site-comparison-construction`: `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`, `AlgebraicGeometry.ProEtale.compactSupportSiteComparison`.
- `def-pur-finite-site-coordinates`: `Sheaf.Paper.FiniteSiteCoordinates`, `AlgebraicGeometry.ProEtale.VectorIntegrationSite.twistComparison`.
- `def-pur-proetale-ordered-integration`: `Sheaf.Paper.ProEtaleOrderedIntegration`, `AlgebraicGeometry.ProEtale.VectorIntegrationSite.orderedIntegration`.
- `def-pur-proetale-frame-integration`: `Sheaf.Paper.ProEtaleFrameIntegration`, `AlgebraicGeometry.ProEtale.VectorIntegrationSite.localIntegration`.
- `def-pur-proetale-vector-integration`: `Sheaf.Paper.ProEtaleVectorIntegration`, `AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorIntegration`.
- `lem-amb-vector-projective-completion`: `Sheaf.AlgebraicGeometry.VectorProjectiveCompletion`, `AlgebraicGeometry.VectorProjectiveCompletion.exists_projective_completion`.

The auxiliary declarations actually used include `VectorBundleZeroSection.π` and `Trivialization`, `VectorProjectiveCompletion.Presentation` and `chartMap`, `Etale.vectorIntegrationCoefficient`, `vectorIntegrationSource`, `vectorBundleIntegration`, `orderedIntegration`, `localIntegration`, `vectorSource`, `vectorSite`, `vectorIntegration`, `compactSupportSiteComparison`, `Etale.rightDerivedLowerShriekOfCompactificationPlusιIso`, both sites' `rightDerivedLowerShriekOfCompactificationBaseChangeMap`, `affineTraceLinearMap_isPullback`, `affineLinearCoefficientPullback`, and `DegreeZeroMapGluing.onSmallerOpen`. No private replacement of a dependency notion was introduced.

Edge cases checked: rank zero uses the existing zero-fold tensor, identity coordinate tower, and GL on `Fin 0`. Empty base and empty finite index type are permitted; `iSup U = ⊤` handles the empty covering axiom. All opens are merely Noetherian, never assumed affine; the base is never assumed separated over k. The coefficient level may be one and the annihilating exponent may be one. Ramified extensions are included without assuming the ramification index divides the quotient level. The coefficient universe remains u+1 and the site retains its existing universes. The arbitrary finite cover universe v is explicitly bound. The normalized H0 isomorphism clause rules out an unnormalized arbitrary choice.

Searches performed (all actual search-service queries are recorded in `searches.jsonl` in the sandbox):

- LeanFinder: `Etale proetale comparison vector bundle trace frame invariance degree zero gluing`: eight algebraic etale-locus, Kaehler and algebraic-trace hits; none gives this statement.
- Loogle: `CategoryTheory.Sheaf`: twelve generic sheaf declarations, no vector trace descent.
- Mathlib grep through msearch: `vectorBundleIntegration|frame.*integration|compactSupportSiteCoherence`: zero hits.
- LeanSearch: `Gluing compactly supported vector bundle traces from local frames under etale proetale comparison`: eight manifold local-frame and generic gluing hits, none gives this result.
- `rg` of the same vector-integration/coherence patterns in `lean/WeilConjectures` and `lean/Sheaf` found the existing constituent definitions and the global-only vector-integration comparison result. It did not find a theorem with this node's frame-action, overlap, concentration and unique-gluing clauses. The literal item-id search in `lean/WeilConjectures` had no match. Searches for the fresh helper names, including the upstream name index, had no collisions.

No new nodes, dependency repairs or statement correction are needed. No statement is disputed. The module uses the existing canonical fixed-coefficient realizations that the item explicitly requests.

Validation: after eliminating overloaded scheme/module sections notation, the final module compiled cleanly through `scompile.py` in both sandbox (15.5 seconds) and library mode (36.0 seconds), with the fixed 60-second limit and two threads. The notation `Γₛ` expands to exactly the scheme sections expression; it changes no object or statement. Definitions contain no `sorry`; the only three postponed proofs are the named theorems with this node's blueprint tags and full natural-language proofs. Dry-run and delivery results are recorded by the prescribed delivery tool.

## Second reading by Q116

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
