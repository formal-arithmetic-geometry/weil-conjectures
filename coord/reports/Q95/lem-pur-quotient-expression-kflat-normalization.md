## Worker report

The delivery states `WeilConjectures.StrictQuotient.quotientExpressionKFlatNormalization`.
Its proof is `sorry`; all helper definitions have actual data or define explicit predicates.
There is no statement correction. The added definition node exposes the precise class of
strict quotient expressions and its representative conditions, which the statement needs.

Hypothesis and clause correspondence:

- Prime and finite coefficient extension: `(l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. These use the recorded Padic coefficient
  extension, including its fixed uniformizer and actual quotient rings. No second coefficient
  ring or uniformizer is supplied.
- Three schemes and the two composable arrows: `{Z X Y : Scheme.{t}} (h : Z ⟶ X)
  (f : X ⟶ Y)`. `_hlZ`, `_hlX`, `_hlY` express invertibility in every residue field.
  The composite is `h ≫ f`, Lean's diagrammatic notation for the source's f after h.
- B, R, and q are the recorded `integralCoefficientCommRingSheaf`,
  `completedIntegralCommRingSheafUnrestricted`, and `normalizedDVRQuotient`/
  `coefficientFiniteQuotient`. Natural-number level n means positive exponent n+1.
- Any finite list, including empty: `r : ℕ`, `P : Fin r → CochainComplex
  (scalarReductionSource l E Y) ℤ`. `hP` is precisely the recorded independent-coefficient
  K-flat predicate. `_hflat i k` uses `SheafOfModules.IsFlatOnSite` on every term.
- Actual generator reductions: the existential N and κ give simultaneous strict complexes,
  with `κ i n : level (N i) n ≅ (scalarReductionExtension ... n).mapHomologicalComplex.obj
  (P i)`. The first equality in the conclusion identifies every actual horizontal transition
  with `coefficientOrdinaryQuotient`, not merely with an isomorphic diagram.
- Finite expression: `Generated l E h f N W K` is the least inductively generated collection.
  Its constructors are exactly inputs, the three degree-zero units, direct-sum total tensor,
  and pullback along f, h and h≫f. This does not quantify over other arrows or impose a
  boundedness restriction. The index W is the actual output scheme.
- Actual strict transitions: `transition` is `NatTrans.mapHomologicalComplex` of
  `coefficientSequenceTransition`, whose definition fixes the actual horizontal map on every
  section. Tensor and pullback constructors use the whole strict complex functors.
  `TensorTransitions` and `PullbackTransitions` assert these induced formulas explicitly on
  pure total-summand tensors and inverse-image unit generators.
- Strict identities and cocycle, and the complex of strict completed-coefficient towers:
  these are built into the data type `CochainComplex (coefficientSequenceModules ...) ℤ`.
  Horizontal maps satisfy the presheaf's functor identity and composition laws, and its
  differentials are morphisms of sequence sheaves. Applying the already defined
  `coefficientSequenceRestriction.mapHomologicalComplex (.up ℤ)` gives a complex in
  `ℕᵒᵖ ⥤ scalarReductionSource ...`, with the actual projection-restricted actions and maps.
  Thus these clauses are enforced by the object type rather than extra arbitrary witnesses.
- K-flatness and flat terms at every finite level: `∀ n, Good l E K n` explicitly conjoins
  the recorded K-flat and flat-sheaf predicates over B_(W,n).
- Derived computation of generators: the e.hom equality specifies the canonical K-flat
  finite-reduction model followed by the inverse of the localized κ, rather than an
  unrelated object isomorphism.
- Derived tensor expression: for every generated pair U,V, level n and normalized tensor
  presentation S, the conclusion supplies Good proofs and an isomorphism e whose hom is
  explicitly `DerivedCategory.Q.map (coefficientEvaluationTensorIso ...).hom` followed by
  `(S.finiteTensorModel n).iso ... hU.1 hV.1`. This is the canonical representative
  comparison, rather than merely `Nonempty` of an isomorphism type.
- Derived pullback expression: `PullbackModel` identifies evaluation of the actual strict
  pullback with ordinary finite-coefficient module pullback, by the actual adjunction-unit
  generator equation. `PullbackComputes` asserts that the universal derived counit is
  invertible on the very input level. These give precisely the derived pullback expression.
- The actual ordinary and derived adjoints and their invertibility: `AdjointModel` provides
  a chain isomorphism a, specifies that its ordinary adjunct equals `transition`, and
  equates the derived adjunct of the localized same transition with the canonical K-flat
  comparison followed by `DerivedCategory.Q.map a.hom`. Quantification over S,D is over
  normalized presentations of those same coefficient operations, not over arbitrary maps.
- Ordinary formula: the final section equation of `AdjointModel` is
  a(b tensor x)=b t(x), and its inverse sends b t(x) to b tensor x. Both use the actual
  quotient-extension insertion section.
  For a generator, the κ transition equality identifies t(x tensor b) with x tensor q(b);
  hence this is exactly (x tensor b) tensor a ↦ x tensor q(b)a. The inverse is determined
  by the same isomorphism and tensor balancing, giving x tensor a ↦ (x tensor 1) tensor a.
  For a unit the identical formula is multiplication with inverse a ↦ 1 tensor a.
- Tensor-adjoint factorization: the conclusion now explicitly requires
  `TensorAdjointEquation`. Its equation is `T.map (tensorComparison m).hom` followed by
  `(D.tensor hmn).hom.app (Q(U_m),Q(V_m))` and
  `(S.finiteClosed n).tensor.map (Prod.mkHom (alpha U) (alpha V))`, equal to
  `alpha (total U V)` followed by `(tensorComparison n).hom`. Here `alpha` is defined as
  the actual derived adjunct of the localized horizontal transition, including the
  exact-localization transport on the restricted target. This states the missing equality
  directly through the recorded strong monoidal comparison, on the very representatives.
- Pullback-adjoint factorization: the conclusion now explicitly requires
  `PullbackAdjointEquation` for all normalized coefficient calculi on W and W'. This
  supplies the evaluation/pullback chain identifications em,en, pinned on the actual
  inverse-image unit generators, and a chain isomorphism chi from scalar extension of
  g_m^*(K_m) to g_n^*(scalar extension of K_m). `ScalarPullbackIdentification` pins chi
  by the equation chi(1 tensor g_m(x)) = g_n(1 tensor x), in every degree and on every
  source-site object. Linearity includes every scalar multiple. These are precisely the
  sheafified balanced coequalizer generators of the canonical comparison; no arbitrary
  isomorphism or unspecified map is substituted. The explicit chain-map equality is
  `extension.map em.hom >> chi.hom >> (finitePull g n).map (ordinaryAlpha K)` equals
  `ordinaryAlpha (pull g K) >> en.hom`. Combined with `AdjointModel` (localization of these
  very adjuncts through the K-flat counits) and `PullbackComputes`, this is the pinned
  ordinary chain-isomorphism formulation of g-inverse-image(alpha) authorized by the return.
  The finite pullback functors already include the canonical constant-coefficient maps.
  Thus both ring identifications are fixed, not extra assumptions. The node
  `lem-sfb-kflat-scalar-comparison-normalization` is explicitly added to stmt_deps.
- Normalized coherent system: `IsNormalizedCoefficientSequence l E W (Q.obj K)` is the
  already recorded universal Hom criterion for the very evaluated transition. This is the
  transition-adjoint-isomorphism condition in `NormalizedDVRTower`, with the strict coherent
  system already supplied by K. It introduces no auxiliary finite-field hypothesis.
- No boundedness, constructibility or flatness of a quotient map is present anywhere.

Dependency declarations used (module → declarations):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` → recorded Padic coefficient rings
  and finite-extension coefficient datum, reexported from CoefficientExtension.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` → the independent-universe
  completed coefficient construction and actual projections, reexported from
  CompletedIntegralCoefficientGerm.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` →
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite` → `SheafOfModules.IsFlatOnSite`.
- `Mathlib.Algebra.Homology.BifunctorShift` → `CochainComplex.mapBifunctor`, used by the
  existing `coefficientTotalTensor`; the sheaf tensor is the recorded localization tensor.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` → the actual pro-etale inverse-image
  conventions and compatible representatives. The helper uses the already published
  sequence module pullback, not a second arbitrary inverse-image functor.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings` → `SheafOfModules.restrictScalars`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel` → the recorded cochain-normalized
  derived extension interface; its finite-level specialization is the existing coefficient
  quotient model, not a new derived tensor construction.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` → the canonical, representative
  normalized ringed-topos pullback/tensor theorem (proof import).
- `Sheaf.Paper.NormalizedDVRTower` → `normalizedDVRModules`, `normalizedDVRQuotient`,
  `normalizedDVRModuleRes`, `normalizedDVRRes`; its normalization criterion is reused through
  `IsNormalizedCoefficientSequence`, retaining the coherent strict representative.
- `Sheaf.Paper.CoefficientRingedSequenceSite` → `coefficientSequenceModules`,
  `coefficientSequenceEvaluation`, `coefficientSequenceTransition`,
  `coefficientSequenceRestriction`, `IsNormalizedCoefficientSequence`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` → `coefficientOrdinaryQuotient`,
  `coefficientFiniteReductionModel`, `CoefficientDerivedSystemTensors`,
  `CoefficientFiniteQuotientCalculus`, `coefficientFiniteQuotientModel`,
  `coefficientFiniteQuotientUnitSection`, `coefficientRestrictionSection`.
- `Sheaf.Paper.IntegralComparisonSequenceSystems` →
  `integralComparisonSequencePullback`, `integralComparisonSequenceGenerator`.
- `Sheaf.Paper.IntegralOperationsWellDefined` → `integralOperationsLevelPullback`,
  `integralOperationsPullbackGenerator`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel` → `coefficientTotalTensor`,
  `coefficientTensorGenerator`.

All already stated proof dependencies are imported, including ChangeOfRingsKFlat,
KFlatTotalTensorModel, SheafRingDerivedCoefficientAdjunction, KFlatScalarComparisonNormalization,
ProEtaleConstantExact, ProEtaleConstantRingMap and CochainPullbackTensorCoherence. None of the
new modules imports IntegralCoherenceTower (a downstream consumer). A read-only graph traversal
confirmed that the additional framework nodes have no path back to this item.

Edge cases checked: r=0 still has all three units and their tensor/pullback expressions;
zero input complexes; empty schemes; arbitrary unbounded integer cochains; n=m gives the
actual identity quotient and action unitor; n=0 is positive exponent one; ℓ=characteristic
is excluded exactly by the stated invertibility hypotheses; no coefficient-map flatness is
used (in particular Z/ℓ²→Z/ℓ is included). Coefficient universe u and site universe t remain
independent: the small site has object universe t+1, morphism universe t, and module universe
max u (t+1). No universe equality is assumed.

Searches: msearch leanfinder query “finite tensor pullback expressions of K-flat quotient
complexes form normalized towers with actual transition adjoints” returned eight general
module-flatness lemmas, no exact match. msearch loogle query `"KFlat", "tensor"` returned
zero hits. msearch grep `quotient.*[Ee]xpression|[Nn]ormalized.*[Tt]ower|KFlat` in
Mathlib/Algebra/Homology returned zero hits. msearch leansearch query “K flat complexes strict
coefficient quotient towers closed under tensor and pullback” returned general module tensor
flatness and HomologicalComplex.tensorObj, no strict quotient-expression predicate. Project
rg found IntegralCoherence.value/Realization, which evaluate already supplied strict inputs
and include completed-operation comparison data; these do not define the least class generated
by this finite list and these three arrows. They are downstream consumers, not prerequisites.
The existing total tensor, restriction, inverse image and normalization definitions are all
reused. `blueprint_refs.py search 'strict quotient expression'` returned zero blueprint nodes;
DAG text search found only this item's statement. No exact theorem exists upstream.

## New nodes

`def-pur-strict-quotient-expressions` supplies the missing least generated class of strict
sequence-complex expressions. Its constructors use the recorded direct-sum tensor and actual
sequence inverse images. Its ancillary declarations name evaluation, the actual transitions,
the conjunction of the existing flat and K-flat predicates, and the two induced-transition
predicates on total-summand tensors and inverse-image unit generators. Source: the item's explicit
finite-expression paragraph and Stacks 07A2, 07A4, 0G7E. The searches above find the constituent
operations and downstream evaluation functions, but no predicate for exactly this class.

The same node also supplies the precise representative conditions
needed in the statement: actual ordinary and derived adjuncts, fixed finite pullback
identification, universal derived computation, and canonical ordinary/derived computation. Its conditions
use the already recorded normalized coefficient calculus and actual local generators. Source:
the item's representative and formula clauses, Stacks 07A6, 07A4 and 0G7E. No existing
predicate conjoins these conditions for a given strict expression and its own horizontal maps.
The expensive section-map elaboration was repaired by specifying its endpoints once in
`horizontal`; the definition interface is delivered in one module.

`def-pur-integral-finite-pullback` records the two already published plain definitions
`WeilConjectures.integralOperationsLevelPullback` and
`WeilConjectures.integralOperationsPullbackGenerator`, with `existing: true` on
`Sheaf.Paper.IntegralOperationsWellDefined`. It defines no duplicate construction and delivers
no extra Lean module. Stacks sites-modules Tag 03D2 (lemma-pullback-module) gives module inverse
image, and Tag 03D3 (lemma-adjoint-push-pull-modules) supplies the adjunction unit used for its
canonical local generator. The exact finite coefficient specialization has no definition-node
owner in the current read clone: DAG rg finds only the well-definedness theorem's declaration
list and downstream consumer statements. The new node cites the recorded coefficient extension,
scheme conventions and general pro-etale inverse image. Mathlib LeanSearch/Loogle/grep find the
general sheaf pullback and adjunction; project rg finds these exact two published definitions.
The verbatim search outputs are retained in the node's mathlib_searches. Blueprint search
`finite.*pullback` returns zero matches; blueprint ancestor is
`def-weil-frobenius-coefficient-twists`. The strict-expression definition cites this new owner
instead of the well-definedness theorem. Its unused derived-change-of-rings reference is removed.

## Second reading by Q95

This is the worker's final rereading, not a claimed independent agent review; the dispatch
brief prohibits starting other agents and assigns independent review to the maintainer.
I reread the source node and all delivered signatures after the return. Generated has only
the three permitted pullbacks, its inputs are exactly Fin r at Y, scalar restriction in
transition is along the actual q, and AdjointModel uses localization of that same transition.
The repaired tensor computation pins its hom explicitly; TensorAdjointEquation now states
the actual derived strong monoidal factorization; PullbackAdjointEquation now states the
ordinary chain-map factorization through a scalar comparison pinned by insertion generators.
The latter localizes to precisely the required inverse-image(alpha), by the retained
AdjointModel and PullbackComputes clauses. These equations repair the missing conclusions
of the returned signature, not merely the explanation in this report.
No statement or source field of the original node changes. Its lean record and stmt_deps
change; the latter add the new definition node and the two landed coefficient-calculus
and scalar-comparison dependencies used explicitly in the repaired signature.

Validation: scompile.py compiles every delivered module separately against the published live
library. Each theorem proof is sorry; no other proof is postponed.

## Repair of returned head 08225af3e60d

The saved packet passed the required initial deliver2.py --no-push check, producing dry-run
commit 8b4e92a4341. I retained its modules and representative construction, and repaired all
three mathematical omissions rather than treating mechanical acceptance as a content review.
Read-only comparison with current main found no differences in the item's other node fields;
the delivery wrapper rebases the packet onto the live branch. No direct git command was run.

F1: replaced the bare Nonempty tensor-isomorphism conclusion by the canonical hom equation
using coefficientEvaluationTensorIso and the finiteTensorModel on Good representatives.

F2: added alpha, tensorComparison and TensorAdjointEquation, and explicitly require the
strong monoidal scalar-extension comparison followed by tensor.map of the two factor alphas.
The equality is no longer left as a prose consequence of other clauses.

F3: added the canonical scalar-change insertion equation and PullbackAdjointEquation for
the ordinary chain adjuncts, using the pinned chain-isomorphism formulation suggested by
the return. This avoids the single-universe specialization of the general scalar comparison
API while retaining independent t and u. AdjointModel already identifies exactly these chain
adjuncts with the derived adjuncts; PullbackComputes identifies their finite pullbacks with
derived pullback. No weaker object-isomorphism assertion replaces the required equality.
Both lem-sfb-kflat-scalar-comparison-normalization and the previously implicit
lem-coef-derived-system-evaluation-calculus are now in the item's stmt_deps.

The generator e clause remains explicitly pinned by kappa; although its existence follows
from the already provided canonical model, this harmless redundancy records the source's
generator computation and introduces no extra hypothesis.

Additional search: msearch leanfinder query “Canonical scalar extension comparison with
inverse image preserves insertion units and transition adjoints of quotient complexes”
returned eight general HomologicalComplex.extend / ComplexShape.Embedding declarations,
no match for these predicates. Project rg found only the section title
CanonicalScalarPullbackIdentification in EtaleProEtaleScalarMate, whose interface is for
etale/pro-etale comparison on one scheme, not these strict quotient-expression adjuncts.
The canonical operations themselves are reused rather than duplicated.

Additional repair checks: read-only DAG traversal visits 454 prerequisite nodes under
lem-sfb-kflat-scalar-comparison-normalization and 719 under
lem-coef-derived-system-evaluation-calculus; neither reaches this item. The unchanged source
clauses and all previously checked edge cases remain covered. I read Stacks 03EL
(sites-modules, lemma-tensor-product-pullback), 0G7E (lemma-pullback-K-flat), and the
07A4 total-complex comparison, plus blueprint det-prop-scalar-six-pullback (1). The scalar
comparison is inverse to the source's chi orientation, as required to compose from scalar
extension after inverse image to inverse image of the ordinary adjunct.

Final compile: scompile.py compiled both delivered modules separately against the live
published build, including the named library modules. StrictQuotientExpressions completed
in about 39 seconds and QuotientExpressionKFlatNormalization in about 6 seconds; no warnings
or errors were emitted. The diagnostic probe was removed. PullbackModel and the new equation
share PullbackIdentification, eliminating the repeated expensive elaboration without changing
its generator formula. No timeout limit or launcher script was changed.

## Repair of returned head 06e701ba3437

The required initial dry run of the retained packet passed as commit 29f129aa616.
I retained both Lean modules verbatim: the return confirms the hypotheses, generator
normalization, tensor model and the two adjunct equations. The only requested repair, H2,
is now made in the actual DAG records. The new existing:true definition node
`def-pur-integral-finite-pullback` owns integralOperationsLevelPullback and
integralOperationsPullbackGenerator. The previously new strict-expression definition cites
this owner in its statement and stmt_deps, replacing lem-pur-integral-operations-well-defined.
It also drops the unused lem-pur-derived-change-of-rings statement reference and edge,
as expressly permitted by the return. The item itself and both Lean modules are unchanged.
The delivery wrapper refreshes and rebases against the live branch; no direct git command
or live-source edit is used.

The new node's clauses read directly against the existing definitions:

- A prime and finite coefficient extension are the explicit section parameters
  `(l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`; coefficientExtensionRing uses the recorded uniformizer.
- Arbitrary schemes in universe t and their morphism are `{X Y : Scheme.{t}} (f : X ⟶ Y)`;
  the level `(n : ℕ)` enters coefficientExtensionRing at exactly `(n + 1)`.
- The finite module pullback is integralOperationsLevelPullback, defined as
  Scheme.coefficientProEtaleModulePullback applied to that precise coefficient ring,
  with ULift only for coefficient/site sizing. The published coefficient functor is
  the canonical adjoint of direct image through the actual constant-section map;
  it introduces no arbitrary map or extra hypothesis.
- The generator is integralOperationsPullbackGenerator: its binders are the actual
  finite module M, source-site object V, and section x. Its body is exactly the unit
  of Scheme.coefficientProEtaleModuleAdjunction at M, evaluated at op V and x. Thus it
  lies on the base-changed object and is the canonical f-inverse-image(x) tensor 1.
- The variables t and u stay independent, with module universe max u (t+1).
  No invertibility, flatness, finite-field or boundedness binder is added.

I reread PullbackIdentification, PullbackModel, PullbackComputes, finitePull and
ScalarPullbackIdentification in StrictQuotientExpressions. Every use formerly assigned
to the well-definedness theorem is precisely one of these two plain definitions;
no well-definedness theorem declaration is used by those predicates. The other theorem
edges retained in the new strict-expression definition are the coefficient-evaluation
calculus (its genuinely proof-dependent canonical model objects) and the scalar-comparison
normalization mandated by the preceding return. Both were explicitly accepted by this return.
The three formerly repaired F1/F2/F3 clauses remain unchanged.

Additional edge checks for this ownership repair: n=0 still means exponent one; any
scheme morphism, including an identity or one with empty source, is admitted; zero module
sections give the actual unit image of zero; no flatness of a coefficient quotient is
assumed. All previously audited r=0, m=n, empty schemes, zero and unbounded complexes,
non-flat quotient and independent-universe cases retain their exact signatures.

Repair validation: scompile.py compiled both delivered modules separately against the live
published library with no errors or warnings (StrictQuotientExpressions about 50.5 seconds;
QuotientExpressionKFlatNormalization about 5.9 seconds). The existing:true owner needs no
new module. The new owner has 187 prerequisite nodes and no dependency path through this
item or StrictQuotientExpressions. Both new definition nodes' bracketed references match
their stmt_deps exactly. The item's only differences from the current read clone are its
already retained lean and stmt_deps fields. The existing owner's lean.statement is verbatim
from the published source.
