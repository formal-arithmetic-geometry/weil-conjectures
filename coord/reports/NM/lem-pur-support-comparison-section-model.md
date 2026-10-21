## Worker report

The module `Sheaf.AlgebraicGeometry.SupportComparisonSectionModel` states
`AlgebraicGeometry.ProEtale.supportComparisonSectionModel` and its
`supportComparisonSectionModel_naturality` clause. Both proofs are `sorry`.
The remaining declarations are concrete expressions or predicates packaging the
specified augmentation and its canonical injective computations. No data is sorry.
The item's statement and dependencies are unchanged.

Source read: Stacks etale-cohomology.tex, section-cohomology-support (09XP),
particularly the injective kernel and restriction construction; current blueprint
main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
thm-pur-rank-one-local-calculation and its proof's final comparison sentence.
The site-comparison normalization is the agent-formulated refinement recorded in
this node; it is not attributed to 09XP alone.

Hypothesis and clause correspondence:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
  Scheme over k: `[T.Over (Spec (.of k))]`. Finite type is the pair
  `[LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact ...]`;
  separatedness is `[IsSeparated ...]`. These are properties of the structure
  morphism, not absolute properness.
- Finite commutative ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  All coefficient categories are ordinary `Sheaf ... (ModuleCat.{u+1} A)`.
  This is the fixed-ring presentation used by the recorded comparison adjunction,
  not condensed coefficients. The recorded finite-coefficient realization
  identifies it with modules over the coefficient ring sheaf. Site objects and
  arrows retain their existing universes; the common larger module universe is u+1.
- Closed immersion: `(i : C ⟶ T) [IsClosedImmersion i]`; the complementary
  open is exactly `i.openComplement.toScheme` and its canonical map is
  `i.openComplement.ι`. Using this named complement introduces no extra hypothesis.
- `F` is the etale module sheaf binder. Its degree-zero source is the dependency's
  `supportComparisonSource T A F`; termwise `comparisonUpperStar` is F_p[0].
- The given resolution is `J : CochainComplex.Plus ...`, `h`, `hh : QuasiIso h.hom`,
  and `hJ : ∀ n, Injective (J.obj.X n)`. Integer indexing allows every lower bound,
  including negative degrees, without selecting a special resolution.
- I is precisely `comparisonLowerStar.mapCochainComplexPlus.obj J`.
  The node's a is `supportComparisonAugmentation T A F J h`, whose source was
  read in PuritySupportCommonInjectives: the ordinary unit followed by nu_*h.
  `ha` and `hI` express the assumed etale injective resolution.
- `θ`, `hθ` and `hunit` spell out the assumption that this resolution represents
  the derived unit using the canonical injective computation. The equation hθ
  characterizes θ by the right-derived unit and the localized h; hunit is exactly
  Qa followed by θ = eta_F. These are the normalization assumptions in the node,
  not an assumption that the three comparisons already have the asserted matrices.
- The first conjunct is the ordinary open-unit equation. Its transport C is
  `comparisonPullbackOpenUnitC`, the sectionwise direct-image identity; beta is
  `comparisonPullbackOpenUnitGamma`. It is the requested equation with beta,
  rather than the dependency's equivalent equation involving beta inverse.
- The next conjunct identifies the restricted etale augmentation with restriction
  of a. `sectionModelOpenAugmentation` uses exactly beta followed by restriction
  of h. Thus the open computation retains the actual given augmentations.
- The next three `Nonempty SupportSectionModelComputation` clauses express the
  T, V, C assertions. Its `et` and `pro` are isomorphisms from localized section
  complexes to the specified derived-section objects. `et_normalization` and
  `pro_normalization` fix them by the given augmentations and the canonical
  right-derived-functor units. Thus this is an existence statement for canonical
  computations, not a definition choosing arbitrary isomorphisms.
  `represents` says et.hom followed by the specified comparison equals Q of the
  direct-image identity followed by pro.hom. For T and V the specified map is
  `finiteComparisonGlobalSections` with its identity-functor unitor removed by
  `sectionModelGlobalComparison`; for C it is the recorded `supportComparison`.
- The support computation uses the existing literal `supportKernelIdentity`.
  The explicit `∀ b : DerivedSupportDirectImageComparison A` equation identifies
  the named `supportComparisonUnbounded` with the derived unit followed by b.b.
  The first factor only converts the existing global-section presentation to the
  terminal-evaluation kernel. The dependency's b is normalized by its
  `kernel_normalization` equation on K-injective complexes, so this quantification
  uses precisely the specified comparison and makes no arbitrary choice of b.
- The final two clauses give equality of the actual degreewise kernel inclusions
  and restriction arrows on I and J. The representative maps in `represents`
  come from the literal identity isomorphisms, so these equalities express
  preservation of these arrows, including after localization.
- `supportComparisonSectionModel_naturality` asserts
  `SectionModelComputationsNatural` for T, V, and C. The predicate quantifies
  over two sheaves, their augmented resolutions, f between the degree-zero source
  complexes (equivalently a sheaf morphism), and t lifting comparison pullback of f.
  It assumes precisely the quasi-isomorphisms/injective terms of such resolutions.
  It states nu_*t a = a' f, the two naturality squares for normalized computations,
  and naturality of the chain identity representative. For the support functor
  this is the induced kernel map. For the restriction functors on V it includes
  in particular the restricted h and beta coefficient identifications above.
  The two canonical computation equations make the computations unique, so the
  quantification over computations does not strengthen the claimed naturality.
- No connecting morphism or boundary compatibility is asserted.

Dependency declarations used (signatures and docstrings read):

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`.
- Mathlib.AlgebraicGeometry.Morphisms.Separated, FiniteType, QuasiCompact,
  ClosedImmersion, and OpenImmersion: `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsClosedImmersion`, `IsOpenImmersion`.
- WeilConjectures.AlgebraicGeometry.DerivedCategories: ordinary etale module
  derived categories; Mathlib `DerivedCategory.Plus`, `CochainComplex.Plus`.
- Sheaf.AlgebraicGeometry.ProEtaleFiniteModules: `FiniteCoefficientModules`,
  `finiteCoefficientRealization` and its exact equivalence; the fixed-ring
  encoding here follows the node's explicit ordinary-module convention.
- def-weil-size-convention has a convention-only lean record: explicit universe u
  and coefficients/modules in u+1 implement it; it has no module to import.
- Sheaf.AlgebraicGeometry.ProEtaleSiteComparison:
  `Scheme.proEtaleSiteComparisonModules`, using `comparisonUpperStar`,
  `comparisonLowerStar` and `comparisonAdjunction` from the upstream Defs module.
- Mathlib.CategoryTheory.Preadditive.Injective.Basic/Resolution: `Injective`
  and `InjectiveResolution`. Our already recorded common-model API uses the
  equivalent explicit integer-indexed bounded-below resolution data.
- Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus:
  `Functor.rightDerivedFunctorPlus`, its unit and the injective computation.
- Sheaf.AlgebraicGeometry.SupportCohomology: `Sheaf.supportedSectionsFunctor`,
  `Etale.supportRestrictionArrow`, `ProEtale.supportSections` and its arrow.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: `Etale.upperStar`;
  the dependency's openImmersionRestriction form is its canonical realization.
- Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence:
  `supportSiteComparisonCoefficientPullbackIso` and its coherence theorem.
- Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized:
  `finiteComparisonGlobalSections`, the actual unit-induced transformation.
- Sheaf.AlgebraicGeometry.SupportSiteComparison: `supportComparison`,
  `supportComparisonUnbounded`, `supportKernelEvaluationIso`.
- Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison:
  `supportEt`, `supportPro`, evaluation functors and identity comparisons,
  `supportDerivedAdjunction`, `DerivedSupportDirectImageComparison`.
- Sheaf.Paper.PuritySupportCommonInjectives: `supportComparisonSource`,
  `supportComparisonAugmentation`, `supportComparisonDerivedResolutionMap`.
- Sheaf.AlgebraicGeometry.ComparisonPullbackOpenUnit: the canonical Gamma and C
  and `comparisonPullbackOpenUnit`.
- Proof imports: Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives and
  Mathlib.Algebra.Homology.HomotopyCategory.KInjective
  (`CochainComplex.isKInjective_of_injective`). Other proof modules are already
  public statement imports. None creates an import cycle.

Edge cases checked: empty T, empty support C (V=T), full support i=id (V empty),
zero ring A, zero sheaf, and arbitrary negative lower bounds of J. All functors
and equations still have the same meanings. No Nonempty or Nontrivial constraint
excludes these cases; no constructibility or local-freeness assumption is added.
The full-support b becomes the final-object comparison by the dependency's
normalization; empty support gives the zero kernel. Naturality includes identity
and zero maps. There is no claim that restriction's kernel inclusion is an
isomorphism for arbitrary support.

Searches (queries and results retained verbatim in searches.jsonl):

- msearch leanfinder: "The identity on section complexes of a proetale injective
  resolution represents the unit induced global sections comparison and supported
  comparison" returned eight unrelated injective-resolution / sheafification hits.
- msearch leansearch: "An etale proetale comparison on supported sections is the
  identity on the common injective resolution kernel complex" returned ordinary
  InjectiveResolution kernel and homotopy lemmas, no site comparison theorem.
- msearch loogle: "Functor.rightDerivedFunctorPlus, Adjunction.unit" returned
  zero hits and reported unknown identifier Functor.rightDerivedFunctorPlus.
  The actual local declaration was then read directly in Mathlib.
- msearch grep: "supportComparison|comparisonGlobalSections" returned zero hits
  in Mathlib. Direct rg searches in lean/WeilConjectures and lean/Sheaf found the
  named comparison dependencies above but no theorem identifying all three
  representatives. Searching the node ID in WeilConjectures returned no hit.
  The proposed helper and theorem names have no hit in either source root or
  dag/lean_names_upstream.json. No duplicate mathematical definition was created.

Validation: scompile.py compiled this file as a fresh sandbox module and as
Sheaf.AlgebraicGeometry.SupportComparisonSectionModel, with no errors or warnings.
Both theorems remain sorry. No statement correction or dependency repair was needed.

## Second reading by NM

A second in-session reading of the node, source and module was performed by this
worker; no independent agent was started, as the dispatch brief explicitly forbids
starting other agents. The maintainer's independent delivery review remains required.

The initial draft omitted an explicit open-augmentation equality and chain-map
naturality. Both are now present. Checked the first equation uses beta in the
forward direction after the C transport. Checked the three computation clauses
name exactly finiteComparisonGlobalSections / supportComparison, and fix source
and target identifications using a and h rather than freely chosen derived
isomorphisms. Checked the supported factorization includes the global/kernel
presentation transport and uses the dependency's normalized b, so compatibility
with the other two arrows is not being substituted for a specification of c.
Checked naturality is restricted to degree-zero sheaf sources and their given
injective resolutions, rather than claiming extra comparison results for arbitrary
complexes. Checked the final literal arrow and kernel-inclusion equalities, the
field/finite-type/separated binders, universes, and zero/empty cases against the
node. No change to the mathematical node was required. This section records an
honest self-check and does not claim an independent second worker's review.
