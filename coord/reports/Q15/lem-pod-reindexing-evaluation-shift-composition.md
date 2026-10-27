## Worker report

The delivery states evaluation normalization, uniqueness, transposition, naturality,
signed shifts on actual Hom complexes and after localization, composition, and identity.
The module is Sheaf.Paper.PodReindexingEvaluationShiftComposition, namespace
WeilConjectures.PodReindexingCoherence. All theorem proofs are `sorry`; definitions
have actual data and the presentation structures only package the specified maps
and their normalization equations. No theorem or definition of another node is copied.

Source read: literature/blueprint/latest/blueprint/sec-poincare-duality/
sk-thm-frobenius/prop-pod-dual-tate-data-compatibility.proof.md, Steps 1, 2 and 4;
Stacks sites-modules.tex, remark-pullback-internal-hom (0GMX), and
sites-cohomology.tex, section-hom-complexes (0A8X) and lemma-internal-hom (08J9).
The current blueprint path differs from the historical path in the node source field;
the current source still identifies the same evaluation and duality construction.

Hypotheses and clauses:

- Prime ell and the finite extension: explicit section variables `l`, `[Fact l.Prime]`,
  `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`.
  Valuation ring, uniformizer, and all quotient rings are exactly the dependency's
  `podReindexingRing`; `some n` means exponent n+1, and `none` means completion.
- Schemes, isomorphisms, invertibility: `{X Y Z : Scheme.{u}}`, `g : X ⟶ Y`,
  `h : Z ⟶ X`, `[IsIso g]`, `[IsIso h]`, and the residue-field `Invertible` families.
  `EssentiallySmall.{u+1}` is the recorded site size convention, explicitly allowed
  by the standing brief. Site objects remain in u+1 and arrows in u; no equality
  of these universes is imposed.
- F and coefficient identifications: every functor is the dependency's
  `podReindexingFunctor`, `podReindexingComplexFunctor`, or `podReindexingDerivedFunctor`.
  These use `podReindexingCoefficient`, uniquely normalized on all finite quotient
  projections, including the completed coefficient ring. No arbitrary coefficient map.
- Ordinary ambient operations: `Closed`, `Models`, `hom`, `total`, and `K` merely
  specialize the recorded CoefficientClosedStructure, CoefficientTensorModels,
  homComplex, coefficientTotalTensor, and cochain-complex category. No boundedness,
  constructibility, perfectness, or derived-completion assumption is added.
- Specified c0: `Comparison.chain_projection` evaluates every actual product factor
  on every slice-site section. `Comparison.derived_model` is the very same
  Hom-model square as podReindexing_hom_resolution_model, including inverse
  augmentation and localization factorization. Thus its `derived` is the comparison
  of that dependency, not an arbitrary natural isomorphism. The all-complex chain
  comparison also states the node's assertion before K-injective localization.
- Specified mu0: `Comparison.tensorChain_pure` fixes every sheafified total-tensor
  generator; `tensor_model` fixes its localization through the recorded K-flat
  models. This is the canonical total-tensor comparison.
- Evaluation equation and unique map: `EvaluationLaws.evaluation` and `.unique`.
  The latter quantifies over every arrow d, not merely isomorphisms. These use the
  Hom-first order of CoefficientClosedStructure.evaluation, as explicitly allowed
  by the node. `symmetry` gives compatibility with the specified Koszul swap,
  so applying the swap yields exactly the node's M-first equation.
- Representative evaluation and transpose normalization: `representative_evaluation`
  uses the existing OneKFlatChainTransposeData, whose `uncurry_pure` is literally
  f tensor x maps to f(x). Its equation localizes that chain map and then applies
  inverse Q(e) for a K-injective resolution e:N→I. The Hom factor is the inverse
  recorded podReindexingHomModel, transported to N by that inverse augmentation.
  The Hom complex is not incorrectly assumed K-flat. No representative is arbitrary.
- All derived arrows and naturality: `EvaluationLaws.transpose` applies to every
  b:L tensor M→N, and `.naturality` has a:M'→M and b:N→N', the required variances.
  The M-first transposition is exactly this one composed with the same symmetry.
- All integer shifts: `ChainShift.formula` fixes each component to (-1)^(a*r)
  with index p-a; actual shiftFunctorObjXIso maps perform every index transport.
  `complexShift` is the existing degreewise-identity mapCochainComplexShiftIso.
  `ShiftLaws.chain` is the chain square; `.derived` is its derived square with
  `signedShift`. The latter is constructed from the existing normalized sourceShift,
  normalized target CommShift, and canonical shift addition. No independently
  chosen derived shift is introduced. comparison_exists supplies these laws and explicitly supplies them for every
  Comparison having the fixed projection and localization normalizations.
- Composition: `siteComp` is the canonical postcomposition comparison. Compositor
  specifies module sections, degree components, and localization components.
  `composition` states both its tensor equation and c_gh = c_h F_h(c_g), with
  all compositor components and Hom variances written out explicitly.
- Identity: Identity specifies the canonical site restriction and its localized
  termwise map. `identity` states that both tensor and Hom comparisons become
  the identities under these fixed identifications.

The declaration `comparison_exists` supplies the normalized comparison and laws.
`evaluation_laws` also makes evaluation and uniqueness available for every
comparison with the specified representative normalization. `composition`,
`identity`, `representative_evaluation`, and `symmetry` state the remaining clauses.
The helper structures are interfaces for these clauses of this same node, authorized
by the human's helper-declaration rule; they are not independent mathematical notions.

Dependencies read and used:

- Sheaf.Paper.PodReindexingHomResolutionModel: podReindexingRing, Modules, Derived,
  Functor, ComplexFunctor, DerivedFunctor, DerivedHom, Q, DerivedFactors, HomModel;
  podReindexingCoefficient_existsUnique, podReindexing_resolution_preservation,
  podReindexing_hom_resolution_model and podReindexing_roundTrip_shift.
- Sheaf.Paper.CoefficientRingedTensorHomModel: CoefficientClosedStructure, its tensor,
  evaluation and transpose, CoefficientTensorModels and its comparison, actual
  coefficientTotalTensor and coefficientTensorGenerator.
- Sheaf.Paper.DerivedPullbackTensorHom (publicly reexported by the first dependency):
  finiteDerivedPullback, finiteIntrinsicClosed, finiteIntrinsicTensorModels and the
  recorded finite/internal Hom interfaces. The present ambient finite category and
  functor are the normalized sectionwise presentations identified by the dependency.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite: Padic.finite_coefficientExtensionRing;
  the coefficient definitions it reexports fix the valuation ring and uniformizer.
- Sheaf.Paper.CompletedIntegralConstantMapOfUniverses and CompletedIntegralCoefficients:
  integralConstantToCompletionOfUniverses, completedIntegralCommRingSheafUnrestricted,
  integralCoefficientCommRingSheaf, completedIntegralCommRingProjectionUnrestricted;
  the dependency uses these exact completed/finite sheaves and their projections.
- Mathlib.AlgebraicGeometry.Sites.Proetale: AlgebraicGeometry.Scheme.ProEt and its topology.
  def-weil-scheme-morphism-properties is a convention node with no declaration;
  Scheme, IsIso, residueField and Invertible are the actual notions needed here.
- Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses:
  CategoryTheory.RingedHomUniverses.sourceShift, homCommShift, LeftFormula,
  RightFormula, leftShift_existsUnique and rightShift_existsUnique. Its already
  landed DAG node lem-weil-pbc-ringed-internal-hom-exact-restriction is added to
  stmt_deps under the standing authorization to add landed notion dependencies.
- Sheaf.SixFunctors.RingedDerivedMonoidalComparisons:
  CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons.
  The specialized compositor in this delivery retains that lemma's ordinary-module
  and K-flat representative normalization, without restricting the pro-etale universes.
- Sheaf.Algebra.Homology.OneKFlatChainTranspose: OneKFlatChainTransposeData and
  oneKFlatChainTranspose, including the comparison, pure uncurry, transpose equation,
  and actual Koszul interchange sign.
- Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal:
  RingedDerivedTensorCoherence and ringedDerived_closed_symmetric_monoidal.
- Proof imports: CochainComplex.exists_isKFlatResolutionIndependentCoefficients
  (Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients),
  SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
  (Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses).
  The recorded homComplex and Mathlib CochainComplex.IsKInjective are public
  imports of the Hom-resolution dependency.

Edge cases checked before writing: zero complexes and zero arrows; empty schemes;
positive level 1 and every higher finite level; completed coefficients with no
boundedness or quotient-tower replacement; a=b=0; either shift negative; odd source
shift and odd Hom degree (the sign is negative); identity g and identity h;
nonidentity scheme isomorphisms; arbitrary unbounded source/target; Hom(P,I) need
not be K-flat; variance a:M'→M; site object and morphism universes distinct.
The differential check uses the ratio (-1)^a between consecutive shift signs.
No counterexample or source/node fault was found; no statement correction.

Searches actually run with msearch.py, group Q15 and this item:

- leanfinder: "Exact reindexing of derived sheaf Hom preserves evaluation transposition
  signed shifts and composition". Eight hits, including exact-functor derived
  shift instances, bifunctor shift component lemmas and Ext transport. They do
  not state the normalized product-Hom comparison and all the node's clauses.
- loogle: "CategoryTheory.MonoidalClosed, CategoryTheory.Functor". Twelve hits,
  including MonoidalClosed.internalHom, ofEquiv and curry/uncurry normalization.
  These are abstract component notions, not this statement.
- grep in Mathlib CategoryTheory: "reindex.*(evaluation|shift)|hom.*shiftIso".
  Twenty-five hits, principally localization/shift comparison maps; no exact match.
- rg in lean/WeilConjectures and lean/Sheaf for podReindexing,
  reindexing.evaluation and the item id. Only the Hom-resolution dependency
  supplies the coefficient-stage product comparison; no existing full theorem.
  The exact item id is absent from upstream WeilConjectures.
- rg for Hom-complex shift declarations found the existing independent-universe
  normalized shift interface, which is used instead of defining another shift notion.

Validation uses only the prescribed scompile.py and deliver2.py wrappers.

## Second reading by Q15

No second reading by a worker: the dispatcher explicitly forbids starting another
agent. As specified by the current direct-delivery workflow, the maintainer's
independent review reads this delivery. The worker's final self-check compared
all the hypotheses and clauses above against the node and the current source;
it is not represented as an independent review.

Final implementation check: explicit coefficient universe parameter u is retained
in derivedInternalHomOfUniverses, even though the module coefficient universe is
max(u+1,u,u)=u+1. Using u+1 for that implementation parameter unfolds to the same
mathematical formula but creates an incompatible opaque localization presentation.
The delivery uses the exact parameter of podReindexingDerivedHom throughout.
Local irreducibility of Padic and coefficientExtensionIntegers prevents generated
record interfaces from unfolding p-adic completions. It changes no definition.
All delivered Lean lines are at most 100 characters; autoImplicit is false;
all six named theorem proofs are sorry: comparison_exists, evaluation_laws,
composition, identity, representative_evaluation, symmetry.

The final scompile.py passed both sandbox and actual library module compilation
with no errors or warnings (the wrapper reported 47.4 seconds for the actual module).
