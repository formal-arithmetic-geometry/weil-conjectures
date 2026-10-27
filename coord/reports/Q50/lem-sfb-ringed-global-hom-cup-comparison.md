## Worker report

Item: lem-sfb-ringed-global-hom-cup-comparison. Module:
`Sheaf.Algebra.Homology.RingedGlobalHomCupComparison`; main declaration:
`CategoryTheory.RingedGlobalHomCupComparison.globalHomCupComparison`.
The only postponed theorem is this declaration, with proof `sorry`. The definitions and
structure types contain no postponed data or internal sorry proofs. The node's mathematical
statement, proof and proof dependencies are unchanged. Three already landed definition
nodes are added to stmt_deps to record the precise interfaces used: the scalar sections,
the normalized global Hom identification, and the coefficient closed tensor model.
There are no new nodes, dependency repairs or statement corrections.

Read the local Stacks source `sites-cohomology.tex`, remark-cup-product (0B6C),
remark-projection-formula-for-internal-hom (0B6D), lemma-section-RHom-over-U (08JA),
and lemma-internal-hom (08J9), including the K-flat/K-injective proof of 08JA.
The first remark defines cup as the adjunct of the tensor comparison followed by two
counits; the second transposes cup/evaluation. The last two fix the global Hom and
componentwise evaluation identifications. The main theorem's docstring follows all
eight proof steps of the assigned node, including the degree-n cocycle normalization,
not just the existence of an unspecified equivalence of cohomology groups.

Hypotheses and clauses, with their Lean rendering:

- A site small in the module universe: `{C : Type u} [SmallCategory C]` and
  `{J : GrothendieckTopology C}`. The universe `u` is explicit and unrestricted.
  A smaller site can be viewed in the coefficient universe; no equality between two
  independently specified universe levels is assumed. The ordinary unbounded sheaf
  derived category uses `[HasDerivedCategory.{u} (Modules R)]`, with Mathlib's actual
  abelian instance. The ordinary module target uses its existing canonical
  `HasDerivedCategory.ofIsGrothendieckAbelian` instance, as required by the recorded
  `ordinaryModuleDerivedInternalHom`. This is a localization-size convention, not a
  new mathematical hypothesis on the site or coefficients.
- Commutative structure ring: `R : Sheaf J CommRingCat.{u}`. `Modules R` is the
  existing `ringedSiteModules`/`SheafOfModules` category, with no replacement category.
- External commutative ring and its structural homomorphism: `A : Type u`,
  `[CommRing A]`, and `s : A →+* Scalars R`. `Scalars R` is the ring of compatible
  global families, so no final site object is needed and `s` need not be flat.
- The induced module direct image is precisely `sections R A s`; its derived functor
  is the existing `derivedSections R A s`. Sections are compatible families and their
  action is `(a*x)_U = s(a)_U*x_U`. Right derivation uses K-injective resolutions.
- The point topos is used in its ordinary A-module presentation `ModuleCat A`.
  Module sheaves on the discrete one-object site with bottom topology are the same
  modules by evaluation at its sole object; bottom topology here means only the
  maximal sieve covers. There is no extra point, lift or morphism given as a hypothesis.
  The ringed-topos pullback is determined by `s` and this sections functor.
- The recorded `derivedInternalHomOfUniverses J R` is the sheaf internal Hom. The
  theorem supplies `S : CoefficientClosedStructure ...` and its actual K-flat model
  `T : CoefficientTensorModels J R S`. Evaluation is `S.evaluation`; its right-tensor
  adjunction and componentwise uncurrying are the existing dependency interfaces.
- `PullbackData.ordinary` and `.adjunction` present the induced module pullback by
  its universal property `ordinary ⊣ sections R A s`. Such a left adjoint, with
  its adjunction, is uniquely the sheafification of U ↦ R(U) tensor_A M, up to the
  unique adjunction-compatible isomorphism. These data occur in the conclusion,
  rather than as a stronger assumption on the input. Additivity and countable colimit
  preservation are recorded as properties of that left adjoint, not input hypotheses.
- `.ordinaryTensor` and `.unit_formula` specify the ordinary comparison by actual
  pure sections, using the sheafification unit and `tensorObjIsoSheafification`.
  The formula is a tensor of the two ordinary unit sections, fixing the canonical
  comparison rather than allowing an arbitrary monoidal isomorphism.
- `.left`, `.epsilon`, and `.isLeftDerived` supply total derived pullback.
  `ScalarFlat` means K-flat and flat in every degree in the native module category;
  `.flat` asserts preservation of these models. `.derivedAdjunction` has right
  adjoint the actual K-injective `derivedSections`. `.adjunction_formula` identifies
  its hom-equivalence on complexes with localization of the ordinary complex
  adjunction, using the actual left comparison and right-derived unit maps.
- `.tensor` is natural simultaneously in the two derived arguments. Its
  `.tensor_formula` is the explicit K-flat representative equation: localize the
  ordinary total tensor comparison, then use `T.iso`; the other path applies the
  left-derived counits and the native coefficient tensor comparison. Thus this is
  the canonical tensor comparison stipulated in the node, not arbitrary data.
- `cup` is defined, with real data, by `p.derivedAdjunction.homEquiv` applied to
  `p.tensor` followed by `S.tensor.map` of the two counits, in the original order.
- `Comparison.chi` is a natural transformation from `globalHom R A s` to
  `(G.op.prod G) ⋙ ordinaryModuleDerivedInternalHom A`. The domain pair is
  `D(O)^op × D(O)`, so this is contravariant naturality in L and covariant naturality
  in M. `.formula` says chi is the transpose of `cup ≫ G.map (S.evaluation L M)`.
  The native ordinary-module closed API uses `Y tensor X`; `transpose` uses its
  canonical Koszul braiding to convert this to the stipulated `X tensor Y` adjunction.
  It does not change the order in the defining cup/evaluation pairing.
- The source all-degree identification is the existing `HomIdentification`.
  Its `.normalization` fixes the image of each Hom-complex cocycle using the actual
  product projections, K-injective augmentation, and localization/shift maps.
  This excludes an arbitrary rescaling of the Hom identification.
- `.targetIdentification` gives the ordinary-module H^n(RHom) to shifted-Hom
  additive equivalence. `.target_normalization` fixes it on every map from A[-n]
  using the existing `CupHomologyRepresentability` and inverse `transpose`.
  `singleAction` uses the existing single-functor shift, native derived tensor shift,
  single-unit identification and left unitor. The shift adjunction then moves
  `Y[-n] → Z` to `Y → Z[n]`. Thus the equivalence is evaluation-normalized
  independently of the desired final equality. Quantification over normalized
  representability data is nonvacuous: the imported theorem proves their existence.
- `.cohomology_formula` is exactly H^n(chi)(v) = G(v) followed by
  `(G.commShiftIso n).hom.app M`, for every `n : ℤ` and `v : L ⟶ M⟦n⟧`.
  Both sides use the same fixed source and target identifications.
- There are no boundedness, quasi-coherence, perfectness or flatness hypotheses and
  no `IsIso chi` conclusion. The only existential maps are accompanied by their
  universal properties or representative/evaluation formulas.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `Q`, `Qh`, `singleFunctors` and homology functors.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  `CategoryTheory.ringedSiteZerothHypercohomologyOfUniverses`, the H^0 of the
  K-injective derived global sections construction; imported, while the A-valued
  full-complex version is the recorded scalar `derivedSections`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom` and its publicly imported
  `CategoryTheory.derivedInternalHomOfUniverses` with representative comparisons.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `CategoryTheory.ringedDerived_closed_symmetric_monoidal` and its tensor coherence
  interfaces, together with `WeilConjectures.CoefficientClosedStructure` and
  `CoefficientTensorModels` from `Sheaf.Paper.CoefficientRingedTensorHomModel`.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`;
  its general geometric definition is imported. Here p is the induced morphism to
  the point, presented on modules by the fixed scalar sections and its adjoint.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`;
  the actual `CategoryTheory.derivedPullbackComplexComparison` and normalized
  representative-square interface are used for the point-site presentation.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`:
  `SheafOfModules.module_pullback_pushforward_adjunction`; provides the ordinary
  module adjunction for the induced geometric morphism, in the proof plan.
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`:
  `CategoryTheory.preDerivedAdjunctionGeneral`; ordinary-to-derived adjunction plan.
- `Sheaf.Algebra.Homology.RingedSiteScalarGlobalSections`:
  `CategoryTheory.RingedSiteScalarGlobalSections.{Scalars,Modules,sections,derivedSections}`.
- `Sheaf.Algebra.Homology.RingedSiteGlobalHomIdentification`:
  `CategoryTheory.RingedSiteGlobalHomIdentification.{globalHom,HomIdentification,Complexes}`.
- Proof imports are the recorded modules for
  `SheafOfModules.PullbackTensorCanonical.pullback_tensor_canonical_shift_unit`,
  `CategoryTheory.derivedAdjunctionShiftCompatible`,
  `CategoryTheory.DerivedInternalHomSectionsModel.derived_internalHom_sections_model`,
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`,
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`,
  `CochainComplex.isKInjective_homComplex_of_isKFlat`,
  `CategoryTheory.derivedAdjunctionOfResolvingClass`, and
  `CategoryTheory.RingedDerivedNative.closedAdjunction`.
  The recorded adjunction-of-natural-bijection leaf is Mathlib's
  `CategoryTheory.Adjunction.mkOfHomEquiv`, with `homEquiv_unit` and `homEquiv_counit`;
  these are available through the imported adjunction APIs.
- `Sheaf.Paper.ModuleCupHomologyRepresentability`:
  `AlgebraicGeometry.Scheme.Modules.CupHomologyRepresentability`,
  `cupSingleModule`, `exists_cupHomologyRepresentability`. This proof dependency is
  public because its normalized interface also occurs in the statement.
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` and
  `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`:
  `DerivedCategory.singleFunctorObjUnitIso` and the native tensor shift instances.

Edge cases checked before writing: n=0 uses the canonical zero-shift laws and the
ordinary left unitor; negative n is included by the integer binder. If L or M is
zero, the pairing and its transpose are zero and the Hom normalization has the
expected zero group. The zero ring A is allowed (a unital s then forces the
compatible section ring to be zero); all constructions remain module adjunctions.
The empty site has its unique compatible family and trivial sheaf module category;
no choice of a final object or nonempty family occurs. An arbitrary nonflat map s,
including A → A/I on the one-object source site, is allowed: scalar extension is
left derived on flat K-flat coefficient representatives, and no underived exactness
is asserted. Unbounded L and M are accepted without truncation; in particular no
K-injectivity of the scalar section Hom complex is assumed. The target normalization
is determined on all A[-n]-maps because the existing representability equivalence
is surjective, so it cannot be chosen retrospectively to force the action formula.

Searches made with msearch.py (all returned successfully):

- LeanSearch: `Derived global sections internal Hom evaluation cup product`:
  eight hits, including `ihom.ihom_adjunction_counit`, ordinary global sections and
  `SheafOfModules.unitHomEquiv_apply_coe`; none states this derived comparison.
- LeanFinder: `Derived global sections internal Hom cup evaluation comparison induces
  application of derived global sections on shifted Hom`: eight hits concerning
  ordinary sheaf sections and LightCondensed internal Hom, no match.
- Loogle: `"DerivedCategory", "Hom"`: twelve hits concerning the localization,
  shifts and single-functor comparisons, no cup/evaluation comparison.
- Mathlib grep: `global.*[Hh]om.*[Cc]omparison|[Cc]up.*[Ee]valuation` in
  CategoryTheory: no hits.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  global Hom comparison and cup/evaluation: no existing theorem for this point-site
  ordinary-module statement. Found and reused scalar global sections and normalized
  global Hom identification. The generic `RingedSiteGlobalHomDirectImage` has a
  general ringed-site target plus Leray/global sections on that target; it is not
  this ordinary-module presentation. Its existing cup helper requires a
  `RingedTensorEdge` between two sheaf-module derived categories, rather than the
  point's ordinary-module category. The older global cup API fixes A=Gamma(R), so
  it cannot render the arbitrary structural map s in this node. No private copy of
  either sections or internal Hom is made. Pure section normalization is written
  directly with existing tensor/sheafification maps, not defined as a second notion.

No STATEMENT-DISPUTED finding and no node fault. The compile initially exposed a
fixed-versus-supplied target localization instance mismatch, corrected by using the
existing canonical target instance, plus explicit tensor endpoints/colimit sizes and
the published namespace of the complex comparison. Those were implementation errors;
the mathematical statement did not change. Validation uses only the prescribed
single-file scompile wrapper, with module mode, autoImplicit false and the default
60-second limit. Final dry-run and delivery results are checked by deliver2.py.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
