## Worker report

The delivery states `lem-pod-specified-hom-scalar-evaluation` in
`Sheaf.Paper.SpecifiedHomScalarEvaluationArbitraryScheme`. Both new theorems have
`sorry` as their whole proof. It introduces no definition or axiom and changes only
this node's `lean` field. The main declaration is
`WeilConjectures.specifiedHomScalarEvaluation_arbitraryScheme`; the companion
`WeilConjectures.specifiedCompletedHomScalarChain` states its chain normalization.

I read the node, all its statement-dependency statements and Lean records, and the
recorded source interfaces, including the generic ringed-site interfaces publicly
retained by the ordinary-module presentation modules. The source read was the
CURRENT blueprint at
`literature/blueprint/latest/blueprint/sec-poincare-duality/sk-thm-frobenius/prop-pod-dual-tate-data-compatibility.proof.md`,
Step 5: coefficient comparisons come from the same evaluation and tensor maps.
The older path in the node has moved in the current blueprint. I also read Stacks
`sites-cohomology.tex`, `lemma-internal-hom` (08J9), its K-flat/K-injective
representative argument and the adjoining evaluation discussion. This is the
agent-formulated normalization bridge specified by the node, not a claim that
Stacks states the completed comparison identity verbatim.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A prime ell is `(l : ℕ) [Fact l.Prime]`. The fields E and L carry `[Field]`,
  `[Algebra ℚ_[l] _]`, and `[FiniteDimensional ℚ_[l] _]`. The algebra embedding
  `ι : E →ₐ[ℚ_[l]] L` is the inclusion E subset L; the construction depends only
  on that embedding, so no algebraic-closure parameter is needed. The valuation
  rings and fixed uniformizers are the existing `Padic.coefficientExtensionIntegers`
  and `Padic.coefficientExtensionUniformizer` used by the recorded quotient towers;
  the statement chooses no different uniformizer or quotient system.
- W is any `Scheme.{u}`. `_hl : ∀ x : W, IsUnit (l : W.presheaf.stalk x)` renders
  invertibility of ell on W. There is no finite-field datum, structure morphism,
  separatedness, quasi-compactness or finite-type hypothesis. The coefficient
  interface uses the same common universe as the recorded constructible category;
  its site objects are in u+1 and site arrows in u, with modules in u+1. The site
  object and morphism universes have not been identified.
- R and S are `completedIntegralCommRingSheafUnrestricted l E W` and its L version
  on `Scheme.ProEt.topology W`; `integralTowerModules` is their actual module-sheaf
  category. M and N belong to its ambient `DerivedCategory`.
- `hM`, `hN`, and `hH` are separately the three predicates
  `sfIntegralConstructible l E W M`, the same for N, and the same for
  `(integralDerivedInternalHom l E W).obj (op M, N)`. This predicate includes
  derived completeness, constructible reductions at every positive level, and
  one uniform finite cohomological interval. In particular hH is retained, even
  though the comparison definitions only need its completeness component.
- T is the existing `integralOrdinaryDerivedScalar l E L ι W`; C is the existing
  `integralScalarExtension l E L ι W`. The ambient H_R and H_S are the existing
  `integralDerivedInternalHom`. These have the node's module-sheaf endpoints;
  the ordinary ModuleCat presentation of the generic Hom is not substituted.
- Each chi_Z is exactly `(scalarCompletion l E L ι W).app Z`, and its inverse
  is expressed through `scalarCompletionIso`. `scalarCompletion_existsUnique`
  fixes this natural transformation on good representatives to
  `integralScalarCompletionChain`, whose unshifted coordinates are the quotient
  maps and whose shifted-product coordinates are zero. Thus this uses the
  quotient-augmentation comparison of the finite-free comparison node, through
  the already recorded scalar-operation presentation, not a fresh isomorphism.
- Gamma is `scalarHomOrdinary l E L ι W M N`. Its definition is
  `coefficientBaseChangeHom` for the existing closed structures and normalized
  scalar tensor comparison, so it is precisely the transpose of T(evaluation).
- Theta is `(scalarHomCompleted ... hM.1 hN.1 hH.1).hom`. This is the existing
  specified completed operation comparison, also used by
  `integralHomScalarComparison` in `DerivedPullbackTensorHom`.
- The first main conjunct is chi_H followed by theta equals gamma followed by
  `H_S.map (Prod.mkHom chi_M.inv.op chi_N.hom)`. Lean's `≫` writes composition
  in application order, so this is the displayed equality in the node. In
  particular the inverse is on the contravariant M input, not on N.
- The second conjunct first transports theta back to ordinary endpoints by
  chi_H on the source and `H_S(chi_M,chi_N⁻¹)` on the target. Its inverse
  `CoefficientClosedStructure.transpose` equals the inverse `scalarClosedTensor`
  comparison followed by T of the recorded evaluation. The API's tensor order
  is Hom-first. The symmetric monoidal Koszul switch gives exactly the node's
  M-first formula, with the same switch on both sides.
- The chain companion quantifies over arbitrary complexes P, I and Q, with
  `integralOperationsGoodComplex` on P and Q (K-flat with flat terms),
  `[I.IsKInjective]`, and `q : Q ⟶ homComplex ... P I` with `[QuasiIso q]`.
  Its constructibility predicates are exactly hM, hN and hH in the normal
  representative presentation M = Q(P), N = Q(I). Any original resolution
  P → M and N → I gives these identifications after localization.
- The target of the existential chain map delta is
  `homComplex (P tensor S) (coefficientHomResolution.obj (I tensor S))`.
  `specifiedHomResolutionUnit l L X` is the existing fixed augmentation j,
  not a new K-injective choice. The first predicate of the unique existence
  applies `coefficientHomSectionEvaluation` to scalar generators and equates
  it with j applied to `integralOrdinaryTensorSection ... (s*b)` of the actual
  `coefficientHomComponent` of q(x), evaluated at m over the identity object
  of the localized site. This is literally j(q(x)(m) tensor sb) in every degree,
  every site object and all four local sections/scalars x,m,s,b. Delta is a
  morphism of complexes, so restriction and signed-differential compatibility
  are included, not extra assumptions.
- Its second predicate equates the localization of delta with the completed
  comparison, conjugated by the actual chi maps and the fixed scalar and Hom
  resolution factorization maps. The factor from q is followed by Hom of the
  R-side fixed K-injective augmentation, then the inverse
  `coefficientHomResolutionIso`; the S-side uses the direct factorization at
  the end. These are the prescribed localized augmentation identifications.
  This equality for every permitted P,I,Q,q renders representative independence
  and equality with the specified operation comparison. No arbitrary comparison
  or existence-only natural isomorphism is supplied as a hypothesis.

Dependency declarations used (all are retained, not copied):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` publicly retains
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing`, and states `Padic.finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
  `def-weil-scheme-morphism-properties` is explicitly a convention node with
  no declaration of its own; invertibility is the local-ring `IsUnit` predicate.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the retained completed
  ring sheaf, its projections and constant quotient cone;
  `integralConstantToCompletionOfUniverses` is not replaced by a constant ring.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` publicly retains the
  generic ringed-site `derivedChangeOfRingsIndependentCoefficients` and the
  cochain model interface. This delivery uses the existing finite-free exact
  scalar specialization, `integralOrdinaryDerivedScalar`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`: `integralScalarExtensionOfUniverses`
  and the retained equal-common-universe `integralScalarExtension`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` publicly retains
  `CategoryTheory.derivedInternalHomOfUniverses`; `integralDerivedInternalHom`
  is its completed-coefficient specialization, not the ordinary ModuleCat Hom.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `finiteFreeCompletedScalarComparison`, the quotient-normalized chain and derived
  comparison. In the scalar-operations presentation these are
  `scalarCompletion_existsUnique`, `scalarCompletion`, `scalarCompletionIso`.
- `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange`:
  `CategoryTheory.ringedFiniteFreeHomBaseChange`. The normalized scalar-operation
  specialization uses `scalarHomOrdinary` and `scalarClosedTensor`.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`: `scalarHomCompleted`,
  `scalarIntegralClosed`, `scalarClosedTensor`, `scalarHomOrdinary`,
  `scalarCompletion`, and `scalarCompletionIso`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `integralHomScalarComparison` is precisely
  the restriction of `scalarHomCompleted` to constructible Hom pairs.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`,
  `homComplexFunctor`; their actual product and signed differential are preserved.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`: `CoefficientClosedStructure`,
  `.evaluation`, `.transpose`, `CoefficientTensorModels`, and `.iso`.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`: `coefficientHomComponent`,
  `coefficientHomResolution`, `coefficientHomResolutionIso`, and
  `coefficientHomSectionEvaluation`.
- `Sheaf.Paper.SpecifiedHomScalarEvaluation`: reuse the real helper
  `specifiedHomResolutionUnit`; its main finite-field theorem is not used as
  a substitute for the arbitrary-scheme assertion.

Proof-dependency imports include
`Sheaf.Algebra.Homology.ScalarHomChainEvaluation` (`exists_scalarHomChainEvaluation`),
`Sheaf.Algebra.Homology.OneKFlatChainTranspose` (`oneKFlatChainTranspose`),
`Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeTensor`
(`ringedFiniteFreeHomBaseChange_tensor`), and
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
(`Functor.mapDerivedCategoryFactors`, a Mathlib dependency without a Lean record).
The other proof dependencies are the same recorded resolution, completeness,
change-of-rings, Hom and scalar-comparison modules already imported transitively.

Edge cases checked before drafting and rechecked against the signature: W may be
empty and need not be of finite type over any field; M or N may be zero; a zero
Hom is allowed; L = E is allowed with identity algebra embedding; ramified
extensions use the existing distinct uniformizer towers and their quotient maps;
P,Q may be unbounded despite bounded constructible derived objects; no perfectness
is imposed. For degree-zero sections the formula is unsigned multiplication sb.
For odd input/Hom degrees, exchanging tensor order contributes (-1) on both
sides; the Hom-first convention avoids discarding that sign. No bound on complex
terms or common valuation uniformizer was added.

Searches actually run:

1. `msearch.py ... leanfinder` with query
   `The specified completed internal Hom scalar comparison equals the evaluation transpose conjugated by the canonical quotient completion maps on an arbitrary scheme`:
   eight hits, including LightCondensed.ihomPoints variants and Gamma-Spec
   adjunction evaluation; none is the derived completed coefficient statement.
2. `msearch.py ... loogle 'CategoryTheory.ihom.ev, SheafOfModules'`: zero hits.
3. `msearch.py ... grep 'scalarHomCompleted|specifiedHomScalar|scalar.*[Hh]om.*eval'`:
   fourteen hits in ordinary algebra, ring-extension and presheaf limits files;
   none states the specified completed derived comparison.
4. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for scalar-Hom/completed-Hom/
   evaluation names found the actual existing maps in
   `IntegralOperationsScalarComparisons.lean` and the older
   `SpecifiedHomScalarEvaluation.lean`. I read their full signatures and docstrings.
   The older main theorem has finite-field, separatedness, locally-finite-type and
   quasi-compactness hypotheses; it is not this arbitrary-scheme theorem. Its
   representative theorem is already on arbitrary schemes, but identifies the
   ordinary gamma. The new companion instead identifies the actual completed theta
   with all chi conjugations in the localized equation. It does not redefine the
   chain operation or its augmentation.
5. Search for the item id in `lean/WeilConjectures` and
   `dag/lean_names_upstream.json`: no declaration attached there. Search for the two
   proposed declaration names in Mathlib/project sources: no collision. The DAG
   node's reviewed note itself records the older finite-field theorem as a
   specialization and this item as its intended arbitrary-scheme generalization.

No statement correction, dependency repair, new node, or disputed statement is
needed. The two theorem docstrings carry the full five-step argument and its
representative normalization. All variables/universes are explicit; there is no
file-local notation, local instance or diagnostic command. The first `scompile.py`
run passed both sandbox and library checks (11.2 s and 6.9 s). The final packet is
validated again by the prescribed dry run after its metadata and imports are set.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
