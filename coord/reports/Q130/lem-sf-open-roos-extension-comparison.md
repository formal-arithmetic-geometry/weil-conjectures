## Worker report

The module Sheaf.Paper.SfOpenRoosExtensionComparison states the node in two named theorems, geometry_products and comparison, both with sorry proofs. Its other declarations construct the actual module categories and extension/restriction functors or spell out the normalization proposition. No proof is supplied and no construction contains sorry.

Hypotheses and objects:

- FiniteFieldDatum D supplies the fixed finite field and algebraic closure k; l with Fact l.Prime and _hl : l ≠ D.p supplies the distinct coefficient prime.
- E : Type u with Field, Algebra ℚ_[l] E and FiniteDimensional ℚ_[l] E is the prescribed finite extension. Its valuation ring, chosen uniformizer, finite quotients and transitions are the imported Padic coefficientExtension constructions.
- X : Scheme.{t}, U : X.ProEt and IsOpenImmersion U.hom represent an arbitrary open immersion j : U.left → X, without replacing its domain by an image open. aX is its k-structure; LocallyOfFiniteType and QuasiCompact on aX and U.hom ≫ aX express that both schemes are of finite type over k. No separatedness is added.
- modulesX is ringedSiteModules of completedIntegralCoefficientSheafUnrestricted, the limit of the actual finite constant quotient sheaves. modulesU is modules over its over U restriction. This is exactly the ringed-slice presentation explicitly allowed by the node: ProEt.sliceEquiv identifies Over U with U.left.ProEt. The completed coefficient comparison identifies the restricted completion with B_U and preserves its quotient projections. It is not the discrete constant valuation ring.
- The site retains object universe t+1 and morphism universe t. Sections and modules have universe max u (t+1), containing the site and coefficient extension independently. sliceAbSheafify and sliceAbLocallyBijective construct canonical size/sheafification instances, with no added mathematical hypothesis. HasDerivedCategory binds the chosen localization universes wA,wB independently.
- extension is the actual localizedSystemExtension: direct-sum presheaf followed by module sheafification. restriction is localizedSystemRestriction, literally overFunctor. The three extension instances reuse the recorded exactness components. No arbitrary functor, comparison, or unit is supplied as input.
- Strict towers are ℕᵒᵖ diagrams; n denotes positive index n+1. CochainComplex (ℕᵒᵖ ⥤ modulesU ...) ℤ is an unrestricted unbounded strict tower complex.
- LA, LB and etaA, etaB with IsRightDerivedFunctor give the total right derived inverse limits, including their units. This is an interface for any chosen total derived functor, not an extra existence or product-exactness assumption.

Conclusions, clause by clause:

- geometry_products concludes IsNoetherian for X and U.left; CompactSpace and QuasiSeparatedSpace for both; QuasiCompact U.hom; and IsUnit l in every structure-sheaf stalk on both schemes. These are conclusions, not hypotheses.
- geometry_products also concludes HasExactLimitsOfShape (Discrete ℕ) on both actual module categories and IsIso (piComparison (extension ...) M) for every countable family. piComparison is the canonical map defined by the images of product projections, so its projection normalization is built into the map itself.
- ComparisonAssertions unfolds to existential HA,HB, their actual shifted mapping-cone object equalities hAobj,hBobj, and signed coordinate isomorphisms chiA,chiB. The coordinate equations use the shifted-cone identification followed by biprod.map (𝟙 _) (-𝟙 _). Thus degree p+1 has coordinates P^(p+1) ⊞ P^p and differential (dx,(1-s)x-dy), with towerTransitionEndomorphism the recorded 1-s. These are pinned coordinate maps, not arbitrary biproduct identifications.
- thetaA and thetaB identify LA and LB with these models naturally on complexes. For K-injectives with injective tower terms their normalized unit is explicitly the canonical limit inclusion (iota,0).
- psi is pinned by every product projection, and kappa by both signed projections and every tower level. They are isomorphisms of complexes, and on each signed summand kappa is exactly the canonical product comparison.
- lambda is one natural isomorphism LA ⋙ extension.mapDerivedCategory ≅ termwiseExtension.mapDerivedCategory ⋙ LB. Its localization square is precisely lambda = thetaB inverse, kappa, extension(thetaA), with exact-functor descent identifications displayed. This gives the specified isomorphism in the ordinary unbounded derived category, rather than only cohomology isomorphisms.
- beta is the projection-normalized ordinary-limit comparison. The universally quantified formula for every pair of K-injective resolutions computes the SAME lambda via extension(lim I) → lim Jt. This records independence of resolutions.
- For every strict augmentation gamma and its transition compatibility, the last clause gives chain maps b,b' with coordinates (gamma,0) and (extension(gamma),0). The displayed equality is extension(a_c) followed by lambda equals a_Jc, including all localization identifications.
- The final two clauses identify these arrows with the actual augmentation maps computed using ANY K-injective resolution: the maps into lim I have the prescribed gamma_n followed by the resolution component as every limit projection. dI is normalized by eta. Thus the augmentation arrows are actual induced maps, not freely chosen derived arrows.
- Naturality in strict tower maps is encoded by HA,HB as functors, the two coordinate map equations, natural thetaA,thetaB, and lambda as a natural isomorphism. The augmentation maps are uniquely fixed by their coordinates and the resolution limit projections; consequently strict augmentation squares commute by these same naturality laws. No boundedness or constructibility assumptions occur.

Dependency declarations read and used:

- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, HasDerivedCategory, DerivedCategory.Q, localization at quasi-isomorphisms.
- Sheaf.Paper.CompletedIntegralConstantMapOfUniverses (publicly importing CompletedIntegralCoefficients): completedIntegralCoefficientSheafUnrestricted, completedIntegralCommRingSheafUnrestricted, integralCoefficientSheafSystem, the actual projection and coefficient constructions.
- Sheaf.Paper.FiniteFieldFiber: FiniteFieldDatum; Sheaf.NumberTheory.Padics.CoefficientExtensionFinite and CoefficientExtension: finite-dimensional coefficient fields and coefficientExtensionRing/Transition/Integers/Uniformizer.
- Mathlib.AlgebraicGeometry.OpenImmersion: IsOpenImmersion; Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and ProEt.topology. The scheme-properties dependency is a convention node with no declaration; finite-type notions are Mathlib LocallyOfFiniteType and QuasiCompact.
- Sheaf.CategoryTheory.RingedSiteModules: ringedSiteModules, exactly SheafOfModules.
- Sheaf.CategoryTheory.LocalizedModuleExactForSystems: localizedSystemExtension, localizedSystemRestriction, localizedSystemExtensionAdditive/Limits/Colimits, localizedSystemAdjunction; universe arguments t+1,t,u preserve the independent coefficient universe.
- Sheaf.Paper.ExactProductFunctorStrictLimit: exactProductFunctorStrictLimit, with all signed model, product, resolution, and augmentation clauses read. Its StrictRoosComparison public import supplies strictRoosComparison and towerTransitionEndomorphism.
- Proof imports: Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization (weaklyEtale_localization and sliceEquiv); Sheaf.Paper.SfClopenCoefficientComparison (sf_clopen_coefficient_comparison); Sheaf.AlgebraicGeometry.ProEtaleRingedOpenExtensionProducts (proEtaleRingedExtensionByZero_products); Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact (ProEt.countableProducts_exact).
- Geometric proof leaves are Mathlib: LocallyOfFiniteType.isLocallyNoetherian, QuasiCompact.compactSpace_of_compactSpace, IsLocallyNoetherian.quasiSeparatedSpace, IsNoetherian.noetherianSpace and quasiCompact_of_noetherianSpace_source in Noetherian/QuasiCompact. No separate project module is recorded for those Mathlib leaves.

Edge cases checked: empty open or empty ambient scheme; identity open; zero complexes and zero augmentations; arbitrary negative and positive cochain degrees; nonseparated finite-type schemes; any finite coefficient extension; independent coefficient and scheme universes; arbitrary strict transitions without surjectivity, completeness or Mittag-Leffler assumptions. The index begins at exponent one through n+1. In particular product exactness and quasi-compactness are asserted, not silently assumed.

Searches for existing declarations:

- msearch.py leanfinder: “An exact open extension functor on proetale module sheaves commutes with derived inverse limits of strict towers preserving normalized Roos augmentations”. Eight hits concerned condensed solidification/profinite objects, with no match.
- msearch.py loogle: “CategoryTheory.Limits.piComparison, CategoryTheory.Functor”. Twelve hits supplied piComparison and its projection/preservation lemmas; these give the canonical ordinary map but not this theorem.
- msearch.py grep: “Roos|homotopyLimit|derivedLimit|jShriek.*[Pp]roduct”, CategoryTheory. Zero hits.
- msearch.py leansearch: “Extension by zero commutes with derived inverse limits of towers of module sheaves”. Eight hits, including SheafOfModules.hasLimit and unrelated direct-limit/Ext facts; no match.
- rg in lean/WeilConjectures and lean/Sheaf for Roos, open extension, and derived limit; rg for the node id in WeilConjectures found no declaration. Existing ExactProductFunctorStrictLimit is the generic theorem, not the geometric specialization. CondensedOpenExtensionProducts uses a different internal-module coefficient category and lacks the signed/augmentation normalization. ClopenRoosIntegralDescent is restricted to finite clopen descent. CompletedExchange concerns completed base change over discrete constant rings, rather than arbitrary strict towers over B_W. These are not exact matches and no notion from them is copied.

Source checked directly: literature/stacks-project/proetale.tex, lemma-j-shriek-limits (Tag 09BP), including its exactness, products and closed-complement proof; current main-20261015 blueprint proof of lem-cbc-completed-extension-zero-comparison, final paragraph. No statement correction, disputed statement, new DAG node or dependency repair was needed. The normalization proposition and category aliases are helpers of this node, recorded in lean.declarations.

Validation: scompile.py compiled the full final module in sandbox and module modes, with no errors or warnings (47.7 and 40.4 seconds respectively). Earlier expensive concrete signatures were replaced by an abstract proposition containing the same laws; no timeout limit was raised. Dry-run and final delivery results are recorded by the delivery tool.

## Second reading by Q130

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
