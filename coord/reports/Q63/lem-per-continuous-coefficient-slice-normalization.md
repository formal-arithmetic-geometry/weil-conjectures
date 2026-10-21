## Worker report

Module: `Sheaf.Paper.ContinuousCoefficientSliceNormalization`, namespace
`AlgebraicGeometry.Scheme.ContinuousSlice`. The main theorem is
`continuous_coefficient_slice_normalization`. Every theorem proof is `sorry`;
the auxiliary `modules_exact` is the exact-restriction clause of the same DAG node,
needed to define termwise derived restriction. Both theorem docstrings give the
natural-language proof and source. Definitions contain real constructions, and the
structures package conclusions rather than assume them as theorem hypotheses.

Hypotheses and clauses:

- Prime ell is `(l : ℕ) [Fact l.Prime]`. The finite coefficient field is `(E : Type u)
  with `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The recorded
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer` and positive
  quotient rings provide A, varpi and A/varpi^(n+1). No replacement coefficient datum.
- All schemes use `Scheme.{u}` and the original `Scheme.ProEt` site (objects in u+1,
  morphisms in u). Ring/module values are in u+1; the existing ULift encoding embeds
  coefficients without equating site object and Hom universes.
- The first conjunct quantifies over every X and every U : X.ProEt, with no noetherian,
  dimension, quasi-compactness, or characteristic hypothesis on either scheme.
  `Coefficients` uses the recorded `ProEtaleObjectRestrictionComparison` for sets,
  abelian groups, rings and commutative rings. Its `initial` field names the actual
  `proEtaleObjectInverseImageIndexPoint`; the comparison's `coprojection`,
  `sheafification_isIso` and `sheafIso_inv` fields retain the actual Kan and
  sheafification units, including naturality in sheaves and site objects.
- `ring U T` is constructed by identity maps on C(|V|,T), giving the same underlying
  V under the concrete slice equivalence. `Coefficients.continuous` identifies the
  actual `continuousCoefficientPullback` with that identity composed with the
  normalized inverse-image comparison. `constants` fixes constant functions and
  `coefficient_maps` records the equality for every continuous coefficient ring map.
  Thus these clauses include integral/rational rings, inclusion and quotient maps.
- `Coefficients.finite` preserves any finite constant commutative ring by its actual
  constant-section structural map. `Adic.quotient_constants` fixes each positive
  coefficient quotient to that same map; `transitions` includes every comparable pair,
  including identity levels; `projections` is the residue projection square, and
  `inclusion` is the A-to-E square. `residue` uses the existing reduction followed by
  the inverse of the canonical constant/continuous-function isomorphism.
- `Completion` identifies A_X with the actual `finiteCoefficientLimit`, with each
  `limit.π` fixed to `residue`, and identifies sheafified varpi-localization with E_X
  by `integralCoefficientLocalizationNormalized`. Main conjunct two has exactly the
  noetherian, finite dimension and ell-invertibility hypotheses in the node:
  `[IsNoetherian X]`, `∃ n, topologicalKrullDim X ≤ n`, and stalkwise `IsUnit`.
- `modules` is literal module-sheaf pushforward along composition with U, with identity
  scalar map. `modules_exact` gives additivity and preservation of finite limits and
  colimits. `derived` is the existing `mapDerivedCategory` of this functor, hence
  termwise on unbounded complexes. `ModuleComparison` identifies actual tensor
  pullback with this literal restriction; `unit` fixes its value on inverse-image unit
  sections. `complex_components` and `normalization` fix the derived comparison using
  `DerivedCategory.Q` and the standard factorization; no boundedness is imposed.
- `ExactPull` makes scalar extension along a coefficient isomorphism equal to scalar
  restriction along its inverse. `scalar_sections` is b tensor m ↦ c⁻¹(b)m. Its complex
  and derived comparisons obey the canonical `pbcComplexCounit` equation on every
  complex. `limits` records exactness of ordinary scalar extension, while `ordinary`,
  `derived`, and `normalization` identify the actual inverse-image/tensor construction
  with ordinary exact inverse image. This is asserted for A and E at every site object.
- Main conjunct three accepts `Etale g ∨ IsImmersion g`, with both schemes satisfying
  the same noetherian, dimension and invertibility assumptions. It supplies one `Adic`
  witness, both `ExactPull` witnesses and, for the normalized completed presentations,
  a `CompletedPull`. The latter's isomorphism on B_X is fixed by integral comparison
  and by every finite projection. Rational coefficients use `Adic.rational`.
  `IsImmersion` is locally closed immersion; no assertion makes closed immersions
  objects of the pro-etale site.
- The final two conjuncts give `Ambient` for integral and rational coefficients, for
  arbitrary f and arbitrary U over its source, without any noetherian restriction on U.
  This accepts the specified coefficient morphism with its existing normalization
  predicate rather than assuming it invertible. `ordinary` restricts tensor extension;
  `sections` sends each sheafified tensor to the identical tensor. `complex_components`
  makes this degreewise. `scalar_derived` and `normalization` impose the full counit
  square for restriction of derived scalar extension. `Ambient.pullback` explicitly
  whisks this comparison by the actual geometric inverse image `adicTowerPullback f R`,
  yielding restriction of E_Y tensor^L_(f^-1 E_X) f^-1(-), and the integral analogue.
  Because `sections` quantifies over all scalar and module sections, it also fixes the
  coefficient/constant-section compatibility, without replacing it by arbitrary isos.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`,
  reexporting the coefficient extension constructions from `CoefficientExtension`.
- `Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized`: the recorded sized lisse
  continuous-ring, field/integer and constant-section interfaces; reexported as required.
  The actual completed-coefficient encoding uses the also-recorded continuous sheaves below.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`,
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`, `proEtaleModuleInverseImage`,
  `proEtaleConstantInverseImageMap`, `proEtaleCoefficientInverseImageMap`.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientBasic`: `continuousCoefficientSheaf`,
  integral/rational sheaves and their normalization predicates, finite tower/limit,
  localized coefficient sheaf. Its recorded ring-functions-sheaf theorem has already
  been proved in the live source; no duplicate sheaf condition theorem is introduced.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`:
  `continuousCoefficientImmersionRestriction`, with its coefficient square and
  composition normalizations. Its proof dependencies additionally expose the actual
  maps in `ContinuousCoefficientPullback` and `ContinuousCoefficientCompletion`:
  `continuousCoefficientPullback`, `continuousCoefficientMap`,
  `integralRationalCoefficientMap`, `continuousCoefficientReduction`,
  `discreteContinuousCoefficientIso`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `ProEt.sliceEquiv`, `sliceFrom` and `weaklyEtale_localization`.
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`:
  `proEtaleObjectInverseImageIndexPoint`, `ProEtaleObjectRestrictionComparison`,
  `proEtaleObjectInverseImageRestriction` (proof input).
- `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`:
  `localization_inverseImage_exact`, `existsUnique_localizationInverseImage`, derived
  normalization and coefficient coherence (proof inputs).
- `Sheaf.Paper.BoundedConstructibleTower`: existing `pbcModules`, `pbcExtend`,
  `pbcDerivedExtend`, `pbcRestrict`, `pbcTensorSection`, `pbcComplexCounit`,
  `adicTowerPullback`. These operate on all modules; constructibility is not imposed.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`:
  `proEtaleRingModuleUnitSection`; existing operations supply
  `proEtaleRingModulePullback`, `proEtaleRingDerivedPullback` and its factorization.
- Proof-only imports retain the available modules of every recorded proof dependency:
  the independent-coefficient K-flat resolution, finite constant sections,
  `exists_localizedSiteTensorRestriction`, `ringedTopoiDerivedPullback`,
  `isKFlat_ringedToposPullback` and `IsUnramified`. Flat, open, etale and weakly etale
  interfaces and sheafification/localized ringed sites come through these imports.

Sources: read the actual Bhatt--Scholze PDF, printed pp. 58--62, especially Definition
6.8.1 (any scheme), Lemma 6.8.2, the paragraph before 6.8.6 and Remark 6.8.15. Read all
statement dependency nodes and their recorded interfaces, plus the inverse-image indexing
comparison and tensor-restriction proof interfaces. No statement correction or dependency
repair is needed; no new nodes are introduced.

Edge cases checked: the empty scheme and empty site objects remain allowed (no chosen
point or nonempty hypothesis); continuous functions into any ring on the empty space form
the zero ring. U may be nonnoetherian, non-quasi-compact, and nonmonomorphic. Zero modules
and arbitrary unbounded complexes are allowed. Quotient index zero means exponent one,
and transitions m=n include identity maps; no level is lost. Finite constant rings include
the zero ring. Identity scheme maps are covered. Closed immersions are treated with their
immersion coefficient isomorphisms, not as weakly etale objects. No field topology is
chosen independently: the existing spectral norm construction is used.

Searches:

- msearch.py leanfinder: "Inverse image along a pro etale site object is normalized slice
  restriction on continuous integral rational coefficient sheaves and derived module
  pullback". Eight unrelated normalization/scheme-module restriction hits; no full match.
- msearch.py loogle: "CategoryTheory.Sheaf, CategoryTheory.Over". Twelve hits, including
  `Sheaf.over`, `GrothendieckTopology.overPullback` and over-map identities; generic
  restriction only, no normalized continuous/adic/derived assertion.
- msearch.py grep: `[Cc]ontinuous.*[Cc]oefficient|[Ss]lice.*[Rr]estriction` in AlgebraicGeometry.
  One Mathlib ElladicCohomology documentation hit; no full match.
- rg in live `lean/WeilConjectures` and `lean/Sheaf` for sliceNormalization,
  continuous.*slice, coefficient.*slice; node-id grep in WeilConjectures. No declaration
  of this node. The parent ContinuousRationalDerivedRealization's SiteRestriction package
  was inspected; it is a downstream realization interface, only rational and without
  quotient/ambient integral clauses, so not reused to create a dependency cycle. Its
  source disappeared from the shared checkout during work, consistent with withdrawal;
  this delivery does not import it.

Validation: prescribed scompile.py compiled the module separately in sandbox and library
mode, no diagnostics, 31.6 s and 36.5 s after strengthening the normalizations. An earlier
attempt to infer a complex isomorphism through the functor's displayed field type caused
unnecessary unfolding; it was replaced by explicit degreewise comparison data, retaining
its normalization and passing within the unchanged 60-second limit.

## Second reading by Q63

A clause-by-clause self-check against the open node and final file found and repaired
three omissions before delivery: completion originally gave only abstract isomorphisms,
so `Completion.projections` and `fractions` now fix them; the immersion/etale corollary
now uses the full `Adic` quotient/inclusion witness and `CompletedPull`; and the ambient
derived isomorphism now has the explicit scalar-extension counit square and complex
component equations. The separate complex comparison avoids unfolding chosen functor
representatives during elaboration. All universes and variables are explicitly bound.
This is a self-check, not an independently staffed review: the dispatcher brief explicitly
prohibits starting other agents and assigns independent review to the maintainer.
