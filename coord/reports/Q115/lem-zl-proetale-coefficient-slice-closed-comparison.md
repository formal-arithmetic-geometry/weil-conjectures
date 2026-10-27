## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleCoefficientSliceClosedComparison` states
`AlgebraicGeometry.Scheme.proEtaleCoefficientSliceClosedComparison`. It also gives the
actual sectionwise restriction and inverse-scalar transport, their exact derived
localizations, and definitions packaging the normalized comparison equations. It proves
nothing. Its only postponed proofs are `proEtaleSliceModuleRestriction_exact` (the
exactness of r explicitly asserted by this node) and the main theorem. Both have source
and complete proof docstrings. All other declarations have real data, or package data
and properties without asserting their existence.

Sources read: Hemo--Richarz--Scholbach, *Constructible sheaves on schemes*, Lemma 4.5
and its proof (PDF page containing the start of Section 4.2); Stacks
`sites-cohomology.tex`, lemma-pullback-tensor-product (07A4), lemma-internal-hom
(08J9), lemma-restriction-RHom-to-U (08JB), and lemma-symmetric-monoidal-derived
(0FPT). The arbitrary-ring-sheaf, unbounded assertion is the ordinary ringed-site
assembly in the node's seven proof steps, rather than the condensed or lisse
specialization of the HRS statement.

Hypotheses and ambient objects, individually:

- A scheme X is `{X : Scheme.{u}}`; there are no geometric hypotheses.
- An object u:U→X of the small pro-etale site is `(U : X.ProEt)`, with `U.hom`
  and `U.prop`. These are the existing Mathlib weakly etale objects, with site
  object universe u+1 and morphism universe u; those universes are not equated.
- The canonical equivalence of sites is `ProEt.sliceEquiv`, already exported by
  the recorded localization dependency. The concrete source-site presentation
  of restriction is composition along `MorphismProperty.Over.map U.hom`, which
  is literally its forgetful composition after that equivalence.
- The specified natural inverse-image identification is
  `(delta : ProEtaleObjectRestrictionComparison U CommRingCat.{u+1})`. Its
  coprojection and sheafification-unit fields fix its normalization. The
  distinguished inverse-image module section is obtained from the existing
  normalized module-adjunction unit and the initial inverse-image index arrow
  in `proEtaleSlicePullbackSection`; it is not an arbitrary map.
- O and B are arbitrary `Sheaf ... CommRingCat.{u+1}` on X and U.left. They
  are not constant sheaves. The coefficient identification is precisely
  `c : (proEtaleSheafInverseImage U.hom CommRingCat.{u+1}).obj O ≅ B`.
- `proEtaleSliceCoefficientIso` defines b by
  `(delta.sheafIso.app O).symm ≪≫ c`; it therefore has exactly the node's
  direction O|U→B.
- The category `proEtaleRingModules` is the recorded `ringedSiteModules`,
  hence Mathlib's `SheafOfModules` on the underlying ring sheaf. Every derived
  category is the existing ordinary `DerivedCategory` of all Z-cochain
  complexes, with the existing standard localization instance.
- `S`, `SR`, `SB` and `T`, `TR`, `TB` present the recorded closed structures
  and their actual K-flat tensor/evaluation models. They are presentations of
  the structures supplied by `ringedDerived_closed_symmetric_monoidal`, not
  extra restrictions on coefficients or complexes. Their normalized models
  exclude an arbitrary replacement for evaluation or tensor. The two
  `RingedDerivedTensorCoherence` binders identify the displayed symmetries
  with the Koszul symmetries, including (-1)^(pq) on representatives.

Conclusions and constructions, clause by clause:

- `proEtaleSliceModuleRestriction` is the existing sectionwise pushforward
  along composition, with the identity coefficient morphism. Its separate
  exactness theorem supplies addition, finite limits and finite colimits;
  these give `proEtaleSliceDerivedRestriction`. This is the source-site
  presentation of the recorded exact derived slice restriction r.
- `proEtaleSliceScalarTransport` is exactly the published `scalarRestriction
  b.inv`. Inspection of that definition shows the same underlying groups,
  maps and sheaf condition, with scalar action composed with b inverse.
  `proEtaleSliceDerivedScalarTransport` applies its exact functor termwise
  and localizes. `Normalized` asserts ordinary and derived equivalence.
- F is the recorded `proEtaleRingModulePullback U.hom O B c`, localized by
  the recorded exact `proEtaleRingDerivedPullback`. It is not a replacement
  slice functor introduced as a new inverse-image definition.
- `Data.ordinary` gives the natural module isomorphism F→r⋙E. The
  `ordinary_section` conjunct of `Normalized` sends the distinguished
  inverse-image section of m to m. B-linearity then forces the full formula
  m tensor s ↦ b inverse(s)m. This characterizes the natural isomorphism,
  rather than merely asserting that the two functors have isomorphic values.
  `proEtaleSliceDerivedComparison` is localization of that very isomorphism,
  followed by the canonical composition comparison.
- The tensor maps of r and E are `Data.restrictionTensor` and
  `Data.scalarTensor`. Their `chain` maps are normalized in `Normalized`
  by the identity formula on every actual pure-tensor summand in every
  total degree. `ProEtaleSliceTensorModel` fixes their derived maps by the
  square with the actual exact-functor localization factorizations and
  published K-flat representative isomorphisms. `kflat` is concluded in
  the comparison data, not assumed of arbitrary inputs.
- The unit comparisons are `Data.restrictionUnit`, `scalarUnit`, and
  `pullbackUnit`, normalized on sections by a↦a, a↦b(a), and the
  distinguished inverse-image section a↦b(a), respectively. The latter is
  c under delta because b delta_O=c. Their localized unit equation is the
  `unit_compatibility` conjunct. The unit is written as the coefficient
  ring in degree zero; conjugating by the recorded coherence `unitIso`
  reads the same equation on the monoidal units.
- `tensor_compatibility` in `Normalized` equates the canonical F tensor
  comparison followed by the two localized delta maps with delta followed
  by E of the r comparison and then the E comparison. The F comparison
  `rho` is the published `proEtaleCanonicalTensorComparison`, with its
  retained unique characterization on flat K-flat representatives.
- H is the recorded `derivedInternalHomOfUniverses`, abbreviated by
  `proEtaleCoefficientHom`. `Data.homComparison` is a natural isomorphism
  H⋙F ≅ (F.op.prod F)⋙HB, hence the required h in both variables.
- `restrictionHom` and `scalarHom` are fixed by
  `restriction_hom_normalization` and `scalar_hom_normalization` as the
  transpose of evaluation after the inverse normalized tensor comparison.
  The former is the canonical slice Hom comparison transported along the
  canonical site equivalence. The latter is the scalar comparison with
  precisely its evaluation normalization. The fixed tensor-Hom
  representative model identifies this with the identity on local Hom
  families, products and differentials.
- `hom_transport` writes the complete conjugation equation for h: localized
  delta at H, E of slice Hom, scalar Hom, then HB applied contravariantly
  to delta_L and covariantly to delta_M inverse. Its directions give an
  arrow FH(L,M)→HB(FL,FM). `hom_normalization` also pins h directly to
  the evaluation transpose using the published F tensor comparison.
- `CoefficientClosedComparisonLaws` is a conjunction of the exact three
  requested equations, for every A,L,M and every g:S.tensor(A,L)→M.
  Its first equation is rho inverse followed by F(evaluation), equal to
  tensor(h,1) followed by target evaluation. Its second is target
  transpose of rho inverse followed by F(g), equal to F(transpose(g))
  followed by h. Its third is F(Koszul symmetry) followed by rho(M,L),
  equal to rho(L,M) followed by target Koszul symmetry. Lean's `≫`
  reverses the written order of the node's `∘`, as required.
- No constancy, boundedness, quasi-compactness, component bound, finite
  generation, dualizability or lisse hypothesis occurs.

Dependency declarations used (recorded source modules and relevant signatures
were read, including their docstrings):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `Scheme.ProEt.sliceEquiv`, `sliceFrom`, `weaklyEtale_localization`.
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`:
  `ProEtaleObjectRestrictionComparison`, `proEtaleObjectInverseImageIndexPoint`.
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`:
  `ringedDerivedRestrictionGeneral`, `ringedOverFunctor_exactGeneral`.
  The new wrapper is the concrete equivalent source-site restriction, not a
  second definition of the abstract slice restriction.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.pushforward`, `overFunctor`; the latter is the literal
  over-site form identified by `ProEt.sliceEquiv`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` publicly exports
  `proEtaleRingModules`, `proEtaleRingModulePullback`,
  `proEtaleRingDerivedPullback`, `proEtaleRingModuleAdjunction`; these
  arbitrary-ring operations are used, despite the module's constant-ring name.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `RingedDerivedTensorCoherence`, `ringedDerived_closed_symmetric_monoidal`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses` publicly retains
  `ringedInternalHom_restriction` and exports the independent-universe Hom.
  Its old equal-universe slice signature is not imposed on X.ProEt: the
  canonical slice comparison is expressed by its evaluation characterization
  on the equivalent source site in this owning node's comparison data.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `ProEtaleTensorModel`, `proEtaleFlatRepresentatives`,
  `proEtaleCanonicalTensorComparison`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`: `CoefficientClosedStructure`,
  its `tensor`, `evaluation`, `transpose`; `CoefficientTensorModels`,
  its `iso`; `coefficientTotalTensor`, `coefficientTensorGenerator`.
- `Sheaf.Algebra.Homology.ScalarInternalHomData`:
  `SheafOfModules.scalarRestriction`, with its exactness instances.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryNatIso`, `mapDerivedCategoryCompIso`, with
  Mathlib's `mapDerivedCategoryFactors` and `mapDerivedCategorySingleFunctor`.

Both already-landed presentation nodes `def-coef-ringed-tensor-hom-model` and
`def-sfb-scalar-hom-comparison-data` are added to stmt_deps because their actual
interfaces are used in the signature. No original dependency is removed. No new
DAG node or dependency repair is needed. The source-site transport and all map
normalizations belong to the notion of this item and are listed in
lean.declarations. No statement correction or dispute is needed.

Edge cases checked: U the terminal object/identity scheme map, U empty and X
empty (restriction has its empty-site interpretation); zero coefficient ring,
zero modules, and zero complexes; c the identity and a nontrivial ring
isomorphism (b inverse action is retained); degree-zero modules and tensors
in arbitrary negative and positive cochain degrees (the actual signed total
complex is used); nonconstant O and unbounded L,M. No map out of evaluation
is inverted. The only inverses are isomorphisms already specified in the node.

Searches for an existing declaration:

- msearch LeanFinder: “Exact inverse image along an object of the proetale
  site with isomorphic coefficient rings is closed symmetric monoidal and
  agrees with slice restriction”: 8 hits on condensed monoidality and etale
  site definitions, no exact matching normalized comparison theorem.
- msearch LeanSearch: “Inverse image of derived sheaves of modules along an
  object of a site preserves internal Hom and evaluation”: 8 hits, including
  `SheafOfModules.evaluation` and ordinary pullback adjunctions; no theorem
  containing this transported derived comparison and its three equations.
- msearch Loogle: `SheafOfModules.restrictScalars,
  CategoryTheory.MonoidalClosed`: 0 hits.
- msearch Mathlib grep: `proEtale.*[Cc]losed|[Ss]lice.*[Cc]oefficient`: 0 hits.
- Source/project rg by item id and by `proEtaleSlice`,
  `coefficientClosedPullbackMap`, and scalar transport: existing scalar
  restriction and ordinary scalar-extension ring-iso constructions were
  found and reused; no existing declaration states the whole item.
  The interrupted turn's exact query/results are retained in searches.jsonl.

Validation: scompile.py compiled the complete module both as sandbox and as
its library module, with no warnings or errors (29.7 s and 24.0 s on the
successful pass). The earlier inline-record elaboration timeout was repaired
by factoring its unchanged representative square and comparison equations
into `ProEtaleSliceTensorModel` and `Normalized`. The 60-second limit was
never raised. There is no local/global library build.

## Second reading by Q115

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
