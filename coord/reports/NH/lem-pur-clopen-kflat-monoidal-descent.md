## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatMonoidalDescent` states
`AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.clopen_kflat_monoidal_descent`.
Its single postponed proof is exactly `by sorry`. All helper data are actual applications
of recorded constructions; no new mathematical notion or construction is postulated.
The natural-language statement, source, accepted seven-step proof and proof dependencies
are unchanged. Added two already-landed statement dependencies solely because their
recorded constructors occur in the signature: `lem-sf-ringed-derived-native-tensor` and
`def-coef-ringed-tensor-hom-model`. Their dependency closures (228 and 208 nodes) do not
reach this item, so these additions introduce no cycle.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A scheme is `X : Scheme.{t}`; the finite set is `I : Type w` with `[Finite I]`.
  The independent index universe is retained; no nonempty assumption or enumeration is used.
- The component schemes and embeddings are `Y`, `j`, with both immersion instance
  families. `hdisjoint` states pairwise disjointness of the image sets; `hcover` is
  precisely pointwise coverage of X.
- The small sites are `topology X` and `topology (Y i)`, with object universe t+1 and
  morphism universe t. The ring is `R : Sheaf (topology X) CommRingCat.{max u (t+1)}`.
  The module universe is max u (t+1); the standard derived morphism universe is
  max (u+1) (t+2). No equality between either site universe or the coefficient parameter
  is imposed. Increasing u includes every coefficient size in the fixed convention.
- `clopenTensorRings` is the recorded component ring restriction, and
  `clopenTensorModules` is the recorded `ringedSiteModules`, with the actual forgotten
  commutative-ring sheaf. `clopenTensorRestriction` is the recorded sectionwise
  `clopenModuleRestriction`; `clopenTensorComplexRestriction` is its degreewise functor.
- `derivedRestriction` specializes the dependency's
  `ClopenLocalization.derivedRestriction` at precisely these module and derived universes.
  `factors` is Mathlib's `mapDerivedCategoryFactors`, typed as a natural isomorphism
  Q followed by restriction to restriction followed by component Q. This is the exact
  comparison specified by the unbounded localization node's normalization clause.
- Unbounded complexes are `CochainComplex ... ℤ`; there are no truncations. The actual
  total tensor is `coefficientTotalTensor`. `TotalNormalization j R h b` pins the ordinary
  tensor comparison by `clopenTensorPure` and pins b on every actual
  `coefficientTensorGenerator` of arbitrary degrees p,q with p+q=n. These generators
  are the sheafification pure tensors followed by total-summand inclusions. Thus this
  is precisely the dependency's normalized b, rather than an arbitrary chain iso.
- The derived tensor and its associator and unitors are the existing
  `RingedDerivedNative.monoidal`, and symmetry is `RingedDerivedNative.symmetric`.
  The helper instances merely expose these existing structures. The native tensor node
  identifies them with K-flat totalization and proves the representative constraint
  squares; the recorded closed-symmetric-monoidal dependency uses these same native data.
- `Comparison j R` is a natural isomorphism between the actual bifunctors tensor then
  derived restriction, and pairwise derived restriction then component tensor. This
  expresses all derived objects and arbitrary morphisms simultaneously; its `.symm`
  is the inverse natural isomorphism. No roof, resolution, or representative is chosen.
- `ModelNormalization j R b c` quantifies over all P,Q, both K-flat hypotheses and
  both degreewise flatness hypotheses. It states
  r_D(t_PQ) ; c_(QP,QQ) ; (kappa_P tensor kappa_Q)
  = kappa_Tot ; Q_i(b_PQ) ; t'_rP,rQ.
  This is the node's displayed composite, after moving its isomorphisms to opposite
  sides. `hiP` is a universally quantified proof argument for the component computation
  iso, not an added geometric assumption: K-flat detection in the recorded dependency
  produces it from hP for every P. The component computation only needs the first
  factor K-flat, so no redundant component proof for Q is required. The model predicate
  uses precisely flat-term K-flat pairs; arbitrary K-flat inputs are not demanded.
- The existential c satisfies this model formula. The quantified `∀ c', ... → c'=c`
  is uniqueness among every natural bifunctor isomorphism having that formula, even
  those not given a monoidal structure. This supplies representative independence and
  unique inverse as well as naturality, rather than uniqueness just among braided data.
- The existential family d consists of `Functor.Braided` structures on exactly these
  derived restrictions. Its inherited `Monoidal` data include natural tensorators,
  associativity and both unit equations; `LaxBraided` is the symmetry equation for
  the native Koszul braiding. `braidedComparison ... (d i) = c` explicitly identifies
  its inverse tensorator with the very same unique c.
- `unitComparison` is the composite r_D(native unit-to-Q(R[0])), kappa_(R[0]),
  Q_i(singleMapHomologicalComplex), Q_i(single of the ordinary ring-unit comparison),
  and the inverse native component unit-to-Q(R_i[0]). Its only scalar map is
  `clopenTensorUnitComparison`; no arbitrary ring or unit identification is supplied.
  `braidedUnit ... (d i) = unitComparison ... h` fixes the same monoidal structure's unit.
- `familyBraided j R d` is actual Mathlib `Functor.pi'` braided data, using the existing
  `Pi.monoidalCategory` with componentwise tensor, unit and constraints. The theorem's
  first conjunct asserts exactly that tuple functor's `IsEquivalence`. Together these
  assert the claimed symmetric monoidal equivalence, with no transported product tensor.
- Empty products, empty components and zero coefficient sheaves are included without
  an exclusion. No nonzero, nonempty, characteristic, flat-ring-map or boundedness
  hypothesis occurs. The empty product braided data exist by the same Pi construction.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and its morphisms;
  Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, `ProEt.topology`;
  Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`;
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing:
  `clopenModuleRestriction`, `clopenRingRestriction`, their actual functor formulas,
  `clopenModuleRestriction_additive`, `clopen_ringed_module_gluing`.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`;
  Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`.
- Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization:
  `ClopenLocalization.Modules`, `modulesAbelian`, `hasDerived`, `restrictionLimits`,
  `restrictionColimits`, `derivedRestriction`, `LocalizationStatement` (including
  restrictionFactors_normalization), `clopen_unbounded_derived_localization`.
- Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetection:
  `clopenTensorModules`, `clopenTensorRings`, `clopenTensorRestriction`,
  `clopenTensorComplexRestriction`, `clopenTensorComparison`, `clopenTensorPure`,
  `clopenTensorUnitComparison`, and `clopen_total_tensor_kflat_detection`.
- Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients:
  `site_derived_tensor_descent_independentCoefficients`,
  `SiteDerivedTensorDescentSpec` (the model predicate and fully faithful extension
  clause), and `siteDerivedTensorIndependentCoefficients`; this is a proof-plan import.
- Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal:
  `ringedDerived_closed_symmetric_monoidal`, `RingedDerivedTensorCoherence`,
  `RingedDerivedTensorComparison`, the six named model normalization predicates.
- Sheaf.Algebra.Homology.RingedDerivedTensorNative:
  `monoidal`, `symmetric`, `tensorIso`, `unitIso`, plus its native constraint squares.
- Sheaf.Paper.CoefficientRingedTensorHomModel: `coefficientTotalTensor`,
  `coefficientTensorGenerator`, `CoefficientTensorModels.iso`.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite: `SheafOfModules.IsFlatOnSite`;
  Sheaf.Algebra.Homology.KFlatIndependentCoefficients:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- Proof-plan imports: Sheaf.Algebra.Homology.KFlatTotalTensorModel and
  Sheaf.Algebra.Homology.RingedTensorComplexConstraints. The sheaf-tensor definition
  dependency is already publicly imported by the total-tensor module.
- Mathlib.CategoryTheory.Pi.Monoidal: componentwise monoidal and braided Pi structures;
  Mathlib's `Functor.Monoidal.μNatIso`, `εIso`, and
  `HomologicalComplex.singleMapHomologicalComplex` give the structural helpers.

Sources read: sites-cohomology.tex at labels lemma-K-flat-resolution (06YS),
lemma-factor-through-K-flat (0G7D), definition-derived-tor (06YU), and
lemma-symmetric-monoidal-derived (0FPT). The latter proof is omitted in Stacks;
this module's theorem docstring retains all seven accepted node proof steps, including
pure-triple associativity, Koszul symmetry, both action-unit equations and extension
by essential surjectivity. No step or naturality clause is silently dropped.

Edge cases checked: I empty forces X empty by hcover; singleton partition; an empty
component; R zero; P or Q zero; negative and odd p,q (Koszul signs stay in the native
braiding); unbounded complexes in both directions. All retain the same canonical
comparisons, and zero categories have unique maps. No counterexample or node fault found.

Searches actually run using msearch.py:

- leanfinder: "Restriction to a finite clopen partition is a symmetric monoidal equivalence
  on unbounded derived sheaf modules normalized by K-flat models". Eight hits, concerning
  light condensed monoidal structures, ordinary ring-flatness and
  `Functor.mapDerivedCategorySingleFunctor`; none is the normalized uniqueness assertion.
- loogle: `CategoryTheory.Functor.Braided, CategoryTheory.Functor.IsLocalization`.
  One hit, generic `Localization.Monoidal.instBraidedLocalizedMonoidalToMonoidalCategory`;
  no clopen theorem or K-flat representative normalization.
- grep: `clopen.*[Mm]onoidal|[Kk][Ff]lat.*[Dd]escent`, CategoryTheory. Zero hits.
- leansearch: "clopen restriction symmetric monoidal derived category K-flat normalization".
  Eight hits: scheme flat restrictions, HasDerivedCategory.standard, FreeMonoidalCategory
  normalization, LocalizedMonoidal and a module-flat tensor theorem; no exact match.
- rg in both lean/WeilConjectures and lean/Sheaf for
  `clopen.*[Mm]onoidal|[Mm]onoidal.*clopen|lem-pur-clopen-kflat-monoidal-descent`,
  then the proposed declaration and namespace. The only initial relevant hits were
  ordinary clopen tensor helpers; no name collision or exact match. The required node-id
  grep in lean/WeilConjectures returned no hits. Broader filename and tensor-calculus
  searches found `ProEtaleFiniteClopenTensorCalculus.finite_clopen_tensor_calculus`:
  its overlapping existence and model equation omit uniqueness, so it does not state
  this node. `ExactMonoidalEquivalenceDerived.nonempty_data` concerns generic equivalences
  with extra functorial-resolution hypotheses and does not state clopen uniqueness.

Validation: all compiles used scompile.py against the live published server library.
The completed module compiled cleanly as both sandbox and library module (library
pass 36.4 seconds). Earlier failures were resolved by fixing the standard module/derived
universe inference and typing the actual localization factors; no universe equality,
extra hypothesis or timeout increase was introduced. All lines are at most 100 characters,
autoImplicit is false, and the only theorem proof is sorry. The final dry run and push
are performed after this report and node metadata are written.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
