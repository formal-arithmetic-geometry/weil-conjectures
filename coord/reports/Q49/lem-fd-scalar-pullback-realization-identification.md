## Worker report

The module `Sheaf.Paper.FdScalarPullbackRealizationIdentification` states
`WeilConjectures.fdScalarPullbackRealizationIdentification`, with `sorry` as its
only postponed theorem proof. All helper definitions have real data; their
functor/complex laws are structural equalities or existing exactness instances.
The repair adds one definition node owning already published common-tower data; no Lean definition is duplicated and no dependency module is replaced.

Sources read: the item's entire statement and eight proof steps; all nineteen
original statement-dependency records and their recorded declarations; the fixed
common-tower and augmentation/counit modules; and the current blueprint's
`literature/blueprint/latest/blueprint/sec-fourier-transform/sk-cor-plancherel/def-fd-trace-function.md`.
The blueprint now locates the trace definition under sk-cor-plancherel; its text
uses the actual pro-etale coefficient category and Frobenius operators. The node
is an agent-extracted normalization lemma supporting that identification, not a
verbatim assertion of the blueprint or Stacks. Stacks 0941's normalized strict
Roos theorem and the supplied eight-step proof are the detailed source of the
statement. No node statement is corrected.

Hypothesis and clause correspondence:

1. Prime ell is `(l : ℕ) [Fact l.Prime]`, explicitly declared in the module's
   variable section. The algebraic closure is `(Ω : Type w) [Field Ω]
   [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`. Finite subextensions and their
   inclusion are `E₀ L₀ : Padic.FiniteCoefficientFields l Ω` and `ι₀ : E₀ ≤ L₀`.
   The recorded `pbcFiniteField.{u}` and `pbcFiniteFieldInclusion` supply the same
   small presentations of these finite fields as the dependencies. In particular
   Ω's universe w is independent of the scheme universe u.
2. U and T are `Scheme.{u}`; `[IsNoetherian U]`, `[IsNoetherian T]`, the two
   Krull-dimension `Fact` instances, and the two stalk-unit `Fact` instances
   render exactly noetherian, finite dimensional, and ell invertible. The supplied
   `fdResidueInvertible` adapter discharges the existing operations' residue-field
   convention without adding a hypothesis. `h : U ≅ T` is a scheme isomorphism.
3. Coefficient rings, positive reductions (Lean n denotes mathematical n+1),
   completed ring sheaves and actual transitions are the existing
   `integralTowerModules`, `pbcIntegralDatum`, and
   `integralOperationsPullbackTowerFunctor`. They are not redefined. Ordinary
   scalar extension C is `integralOrdinaryDerivedScalar`; completed scalar S is
   `integralScalarExtension`; Fs is `integralDerivedPullback`; Fp is
   `pbcActualCompletedPull` with its published unit-compatible strict-tower
   realization. Ordinary G is `pbcActualDerivedPull`.
4. The identity transport I is the recorded `integralDetailedTransport`, computed
   by `fdCoefficientTransport` from the quotient-normalized coefficient identity.
   `FdScalarCoefficientTransport` packages only its scalar presentation square:
   `generators` fixes the ordinary map on sheafified pure tensors, and
   `normalization` fixes its derived isomorphism through the actual cochain
   counits. cU and cT are existential conclusions, not arbitrary map hypotheses.
5. `D : IntegralComparisonSystem l` is the fixed simultaneous realization system
   stipulated by the node. Its pullback/scalar models and its Roos comparisons
   already carry their representative normalizations. It is not a new assumption
   on fields, schemes, resolutions or coefficient maps. Existence is supplied by
   the recorded realization and augmentation/counit dependencies. The statement
   works with any such normalized fixed system.
6. `bE bL : FdCommonStrictTowerModels ... h` are the stipulated normalized b's.
   Their `ambient`, `actual_ambient` and `integral` fields are respectively the
   normalized ambient comparison, its actual-completion presentation on complete
   inputs, and its full integral restriction. Their existence is the already
   stated common-tower lemma, and their `normalization`, `resolution` and
   `actual_normalization` fix exactly the rho and identity transports in the node.
7. `fdScalarTowerComplex` merely reassembles a strict diagram of complexes as a
   complex of strict diagrams, component by component. `fdScalarStrictMap` is
   exactly the existing `scalarPullbackTower` passed through that reassembly;
   it retains all quotient transitions and the specified generator formula.
   It is not a tuple of independently chosen derived evaluations.
8. The canonical tensor/limit comparison is `fdScalarLimitComparison`. Its
   definition uses the constant-tower/Rlim adjunction applied to scalar extension
   of the whole counit, with the ordinary constant/scalar square. This is the
   canonical map of finite-free strict-tower transport, defined before any basis.
   `fdScalarLimitOnTowers` is rho-E, this comparison, the exact scalar localization
   factor, Rlim of the actual d, and rho-L. The `comparison` fields of D's Roos
   models normalize rho as inverse iota followed by H(q); iota has zero shifted
   coordinate. The public strict Roos and common-tower dependencies retain this
   normalization for every injective-term K-injective resolution.
9. `fdScalarLimitRealization` inserts precisely the good-representative
   localization comparisons. `fdScalarLimitAt ... K P e` transports it along
   `e : Q(P) ≅ K`. P is in `integralOperationsGoodComplex`, exactly flat-term
   K-flat, and the scalar-changed representative's goodness is the existing
   `scalarGood` conclusion. There is no K-flatness hypothesis on a quotient term.
10. `fdScalarActualPbc` uses cU, the actual ambient bE, the inverse of the
    existing `pbcScalarCompletedPullIso`, and cT inverse. The theorem's equality
    after `integralDetailedTransport.map` and bL therefore says delta-p is the
    actual PBC alpha-p, on the same coefficient-identity presentations.
    The inverse is the orientation C_U Fp-E -> Fp-L C_T in the question.
11. The first quantified conjunct retains the exact unit equation:
    C_U(kappa-E) followed by alpha-p equals the inverse ordinary
    `pbcScalarOrdinaryPullIso` followed by kappa-L. The latter is the actual
    balanced scalar-adjunction mate, not an input parameter. Both kappas are
    `pbcActualCompletedPullUnit`. The second conjunct asserts precisely the
    injectivity of precomposition with C_U(kappa-E), for complete J and this
    complete target, so the characterization includes uniqueness.
12. `hF` and `hC` are existential conclusions saying pullback is complete and
    ordinary scalar change of K is in the common integral constructible category.
    K itself is in `sfIntegralConstructibleCategory`; its identity with the PBC
    full category is supplied by the recorded characterization. No preservation
    or constructibility premise is imposed on K beyond the node's domain.
13. `fdScalarLimitAt = scalarPullbackOrdinary.hom.app K` identifies the Rlim(d)
    realization with delta-s. The latter is already defined by localization of
    `scalarPullbackChain`, which applies d on BOTH Roos coordinates. The theorem
    uses `scalarPullbackCompleted`, whose definition is chi-U inverse, this
    ordinary comparison, and Fs-L(chi-T), in exactly that order. Here chi is
    `scalarCompletionIso`, with the stipulated quotient/zero-coordinate chain
    normalization. The main framework equality identifies this specified
    alpha-s with `integralComparisonLambda.hom ≫ integralComparisonMu.inv`.
14. The two `fdScalarWholeAdjunct` equalities are in the derived category of
    ENTIRE strict towers. The first is the adjunct of lambda chi-U; the second
    is the adjunct of mu Fs-L(chi-T) delta-s. Their common value now has an
    independent definition, `fdScalarAugmentedRealization`, which never refers to
    lambda, mu, scalar completion, or `scalarPullbackOrdinary`. Its target is
    `coefficientSequenceDerivedRestriction` of `fdScalarReductionTarget`, namely
    S-seq F-seq reduction(K), the system's actual reduction target. It first
    transports K to P and Fs-E to its strict Roos representative; applies the
    inverse constant/scalar square; scalar-extends the source whole-tower Roos
    counit; applies the exact scalar localization factor and Q(d); then inserts
    the inverse `fdScalarTargetComparison` and transports P back to K. Under
    the normalized source Roos comparison this is precisely the unshifted
    quotient projection followed by d, including all strict transitions.
    `FdScalarTargetPresentation.source_iota_zero` explicitly states zero in
    the shifted augmentation coordinate of the ordinary-limit/Roos comparison
    used to normalize that source counit, for every tower complex and degree.
    A target presentation is not an arbitrary comparison: `reductionIso` and
    `quotients` satisfy `CoefficientReductionPresentation`, including all
    horizontal reduction squares; `towerIso` is a strict diagram isomorphism
    and its `generators` field identifies actual system scalar/pullback tensor
    generators with the specified d_m applied to scalar-extended framework
    pullback generators. `fdScalarTargetComparison` uses only these data, the
    exact sequence-pullback localization factor and the universal scalar
    cochain counit. `comparison_isIso` states its invertibility. The theorem
    CONCLUDES existence of such presentations for every P, and states BOTH
    adjunct equalities for EVERY such presentation, so the formulas are not
    vacuous and do not depend on a selected presentation. No target isomorphism
    is postulated as an added premise on the schemes, fields, or K.
15. The last two conjuncts assert equality for every second good representative
    and naturality for every morphism K -> K' in the common full integral category,
    with independent choices of their good presentations. In particular all
    identities descend independently of both good and tower resolutions.

Dependency declarations used (modules and names):

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`; `Mathlib.AlgebraicGeometry.Sites.Proetale`:
  `AlgebraicGeometry.Scheme.ProEt` and its topology.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralStratifiedPerfectCharacterization`, `integralDetailedTransport`,
  `integralDetailedCoefficientComparison`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting the actual integer rings,
  uniformizers, finite quotients and quotient transition constructions.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and its finite quotient cone.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, as used by the recorded good
  representative class; `Sheaf.Paper.IntegralDerivedOperationsOnSlices`:
  the recorded integral derived operations and their Roos representative models.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `integralDerivedPullback` through its
  public integral-operations imports; `Sheaf.Paper.PbcQbarCompletedPullback`:
  the actual completed-pullback functors and their unit-compatible strict model.
- `Sheaf.CategoryTheory.StrictRoosComparison`: `strictRoosComparison`;
  `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses` and its representative comparison.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `finiteFreeCompletedScalarComparison`, `completedScalarComparison`;
  `Sheaf.Paper.SpecifiedPullbackComparisonAlpha`:
  `specifiedPullbackComparisonAlpha`, reexporting `scalarPullbackTower`,
  `scalarPullbackChain`, `scalarPullbackOrdinary`, `scalarCompletionIso`,
  `scalarPullbackCompleted` and `scalarGood`.
- `Sheaf.CategoryTheory.FiniteFreeStrictTowerTransport`:
  `SheafOfModules.finiteFreeStrictTowerTransport`; its canonical adjunct is
  specialized explicitly in the helpers, with `projectionPost` from
  `Sheaf.CategoryTheory.StrictProjectionLimitData`.
- `Sheaf.Paper.PbcScalarExtension`: `pbcScalarCompletedPullIso`,
  `pbcScalarOrdinaryPullIso`, `pbcEmbeddingAmbientTensor`,
  `pbcScalarCoefficientMap`, and the actual ordinary/derived scalar counits.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `IntegralComparisonSystem`, `integralComparisonLambda`,
  `integralComparisonMu`; its public realization-model module supplies
  `integralComparisonConstantAdjunction` and `integralComparisonTowerCounit`.
- `Sheaf.Paper.KFlatScalarComparisonNormalization`:
  `SheafOfModules.ScalarPullback.kflat_scalar_comparison_normalization`;
  `Sheaf.CategoryTheory.FiniteFreeCompletionTransport`:
  `CategoryTheory.finiteFreeCompletionTransport`, used in the proof plan.
- Added statement dependencies: `def-fd-coefficient-comparison-datum`
  (`Sheaf.Paper.FdCoefficientComparison`: `fdCoefficientTransport` and factors),
  `def-fd-finite-pullback-comparison-datum` (`Sheaf.Paper.FdPullbackComparison`:
  `fdResidueInvertible`), and the new `def-fd-common-strict-tower-models`
  (`existing: true` on `Sheaf.Paper.PullbackCommonStrictTowerModels`:
  `FdCommonStrictTowerModels` and its ten helper definitions). The existence
  theorem `fdPullbackCommonStrictTowerModels` is used only in the proof plan;
  `lem-fd-pullback-common-strict-tower-models` stays in proof_deps, not stmt_deps.
  Other stated proof dependencies are imported with proof-only visibility.
- The new target-presentation helpers also use the recorded realization-model
  and system-calculus declarations, publicly reexported by
  `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `CoefficientReductionPresentation`, `CoefficientDerivedSystemCalculus.reduction`,
  `integralComparisonDerivedSequencePullback`,
  `integralComparisonSequencePullback.mapDerivedCategoryFactors`,
  `integralComparisonSequenceScalarModel.ε`,
  `coefficientSequenceRestriction.mapDerivedCategoryFactors`, and
  `integralComparisonLimitToRoos`. These are actual whole-system/cochain maps.

Edge cases checked before and after writing: E₀ = L₀ is allowed by non-strict ≤;
there is no proper-inclusion, unramifiedness, individual d-m invertibility, finite
Tor dimension, or finite-quotient-flatness premise. Degree-zero complexes and the
zero complex fit the unbounded complex and good-representative types. Empty
schemes are not excluded; invertibility and finite-dimension conditions use the
same conventions as the dependencies. The scheme isomorphism may be identity.
All positive coefficient levels are present, with the existing zero-based index
shift. No lower bound on the coefficient/algebraic-closure universe is imposed
relative to the site: the finite field uses the dependency's `Shrink` model and
the completed modules live in u+1 over the Type (u+1), Category.{u} small site.

Searches actually run via msearch.py, plus source rg:

- LeanFinder: "The actual completed scalar pullback comparison agrees with the
  strict Roos tower comparison and counit realization". Eight hits, including
  `PresheafOfModules.pullbackComp`, `SheafOfModules.pullbackComp` and chosen
  pullback counit identities; none has the completed coefficient/strict-Roos
  identification in this node.
- Loogle: "NatTrans, Adjunction.counit". Zero hits; reported unknown identifier
  NatTrans, so this was not an exact type-search confirmation.
- Mathlib grep: "scalar.*pullback|pullback.*scalar", subdirectory CategoryTheory.
  Zero hits.
- LeanSearch: "Completed scalar pullback comparison equals the strict derived
  tower limit map and the counit realization comparison". Eight hits on ordinary
  categorical pullback comparisons and counits, none on this identification.
- rg over lean/WeilConjectures and lean/Sheaf for scalar/pullback and realization
  names found the recorded scalar, quotient-cone and realization interfaces. They
  supply the ingredients but no declaration combining the two requested actual
  identifications. rg by the item's exact id in WeilConjectures returned none.
- Exact helper/theorem-name rg over both Lean roots and dag/lean_names_upstream.json
  returned none, so none of the new declaration names collides.

Validation: the full statement and helpers compiled on the server, in module mode,
with the prescribed scompile.py and 60-second per-file limit. The final dry run
and delivery below repeat the authoritative compile. No library/global build,
manual Git operation, or shared-repository write was performed.

## Second reading by Q49

Self-audit with both the node and finished module open (the maintainer's independent
review is separate): checked all fifteen correspondences above. Initial generic
finite field embeddings were specialized in the theorem to actual finite
subfields of the given algebraic closure, with independent closure universe w.
The coefficient transport is generator- and cochain-counit-normalized, and its
existence is concluded, avoiding arbitrary comparison hypotheses. The Rlim(d)
map is constructed before being identified with either actual comparison.
Both whole-tower adjuncts target the original simultaneous system. Explicit
resolution independence and arbitrary-derived-morphism naturality remain.
The source-based TeX statement is unchanged. No STATEMENT-DISPUTED issue remains.

Repair self-reading, with returned head 832347aaa87f and the current node/module
open: the old report's clause 14 described a common augmentation but its definition
was the mu route itself. That was a mathematical statement mismatch despite a
passing dry run. The current definition was checked factor by factor: no lambda
or mu occurs in it or in `fdScalarReductionTarget`, `fdScalarTargetComparison`,
or `FdScalarTargetPresentation`. The scalar target comparison is pinned before
both routes are compared. The generator equation contains the actual d_m,
source iota has its explicit zero shifted coordinate, and both route adjuncts
are equated to that independent construction. Existence of target presentations
is a conclusion, followed by universal quantification over their choices. The
original Ω universe, E=L case, completion-unit equation/uniqueness, pinned bE/bL,
Rlim(d)=delta-s, resolution independence and naturality are retained.
The new owner node is a definition with an existing record, not a second
existence lemma. Its statement was read against every field of
`FdCommonStrictTowerModels`, including both cone coordinates, the all-resolution
normalization, actual-completion presentation, and full integral restriction.
No definition or theorem of the live repository was changed.

## New nodes

`def-fd-common-strict-tower-models` owns the already published
`WeilConjectures.FdCommonStrictTowerModels` and the ten helper definitions in
`Sheaf.Paper.PullbackCommonStrictTowerModels`, via `existing: true`. It defines
the data of the normalized common strict quotient tower, its two realizations,
resolution-normalized ambient comparison and full integral restriction; it
asserts no existence. The source is the trace-definition opening paragraph's inclusion of bounded
constructible coefficients in the actual pro-etale coefficient category, and
the already specified common-tower data with its Stacks 0941/099N normalization.
LeanSearch returned eight ordinary cone, profinite-limit and quotient-congruence
hits; LeanFinder returned eight categorical shift and affine-limit hits; none
has this model. Mathlib CategoryTheory grep returned zero hits. Source rg found
no upstream declaration, and found precisely the existing Sheaf structure and
helpers. DAG rg found the common-tower existence lemma and this item, not a
separate definition node; blueprint_refs search found none. The searches are
recorded with exact result names in the new node's mathlib_searches. The main
item cites this definition node, and retains the existing theorem only as a
proof dependency. All twelve cited notions of the definition's TeX statement
are exactly its stmt_deps.

## Repair of return 832347aaa87f

1. H3: replaced the mu-defined shared augmentation with the direct source-counit,
   strict d, and cochain-counit target comparison construction described in clause
   14. The theorem supplies a normalized target presentation and equates both
   whole-tower adjuncts with this independently defined map, for all such
   presentations. The zero shifted augmentation coordinate is stated explicitly
   in `source_iota_zero`; `generators` fixes the finite unshifted d_m formula.
2. Mechanical statement-dependency finding: added
   `def-fd-common-strict-tower-models` with the existing structure/helpers record.
   Removed the theorem's id from the extra stmt_deps and kept it in proof_deps.
   The public module import remains because the definition data are used.

The first saved-packet dry run passed at d5c7f0abff6; it was not pushed because
this self-reading found the returned H3 still present. The retained packet was
repaired in place, not reconstructed or merely rebased. The repaired source is
compiled again and receives a fresh authoritative preflight before delivery.

The repaired-packet dry run compiled the module and found one metadata omission:
`import_flags` on the new definition node. Added the required empty list; the
node imports no suspect blueprint flags. No Lean change was needed.
