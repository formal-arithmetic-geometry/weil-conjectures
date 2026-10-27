## Worker report

Module: `Sheaf.Paper.PodReindexingCompletionUnitTensor`.
Main theorem: `WeilConjectures.podReindexingCompletionUnitTensor`.
Additional ambient statement: `WeilConjectures.podReindexingCompletionUnit`.
Both theorem proofs are exactly `by sorry`; there are no other postponed proofs.
The ambient, tensor, coherence, scalar, shift and substitution structures are now
owned by the new definition nodes below. They use the existing coefficient,
completion, tensor and site notions.
No data definition contains `sorry`.

Source read: the current blueprint at
`literature/blueprint/latest/blueprint/sec-poincare-duality/sk-thm-frobenius/prop-pod-dual-tate-data-compatibility.proof.md`,
Steps 1 and 5, and all eight proof steps of the assigned DAG node. The old
source path in the DAG predates the current blueprint directory layout.
The blueprint uses the genuine automorphism pullback and the canonical tensor
comparison; the node refines their quotient-system and representative normalization.
The supplied node statement is unchanged.

Hypotheses and clauses, in order:

- Prime l: `(l : ℕ) [Fact l.Prime]`.
- Finite E/Q_l: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The valuation ring, chosen uniformizer and
  positive quotients are the recorded `Padic.coefficientExtension*` constructions.
  Index `n : ℕ` always denotes exponent n+1, including the first positive quotient.
- The small pro-etale site is `Scheme.ProEt` with `ProEt.topology`.
  The coefficients and their limit projections are the existing
  `integralCoefficientCommRingSheaf`,
  `completedIntegralCoefficientSheafUnrestricted` and
  `completedIntegralCommRingProjectionUnrestricted`.
- The scheme isomorphism is `(g : X ⟶ Y) [IsIso g]`. Invertibility of l on
  each scheme is `[∀ x : X, Invertible (l : X.residueField x)]` and the
  corresponding Y instance. No nonemptiness, finiteness, separation, or
  Noetherian hypothesis is imposed on X or Y.
- F is `podOrdinaryReindex`, defined by the exact derived functor of
  `isoReductionIntegralInverse`. That existing functor is actual sectionwise
  inverse image, with the completed coefficient isomorphism normalized by all
  quotient projections. Finite F_n is the recorded `isoReductionFiniteDerived`.
- R_W is `(podReindexCalculus l E W).reduction`, using precisely
  `coefficientDerivedSystemEvaluationCalculus`; F_bullet is the recorded
  `integralComparisonDerivedSequencePullback`. L_W is
  `coefficientSequenceLimit`, the total derived limit after scalar restriction.
  These are functors on the ambient, unbounded derived categories.
- The two natural identifications are `PodCompletionReindex.reduction` and
  `.limit`, both natural isomorphisms of the stated functors. `.evaluation`,
  `.restriction` and `.finite` retain the finite coefficient identifications.
- Every quotient arrow is retained by the strict system category and by
  `QuotientTransition`; `QuotientGenerators` fixes the chain comparison on
  p tensor b. `FiniteModel` relates that map to the actual derived comparison,
  and `ReductionEvaluation` fixes its finite evaluations.
- Every limit projection is fixed by `LimitProjection`. `Unit` and `Counit`
  are equations in the full derived system categories, before evaluation;
  they use the actual adjunction carried by the recorded calculus. They do
  not infer equality of system maps from their separate finite evaluations.
- The specified completion unit is identified with the original quotient
  completion unit by `CompletionUnits`. This is the original identity-scalar
  normalization used by `finiteFreeCompletedScalarComparison` for E=E.
  `CompleteUnit` asserts invertibility only for
  `IntegralOnSlice.IsComplete`; it says nothing of this kind for ambient
  incomplete objects.
- `podOrdinaryToCompleted` is literally F(unit), followed by `.limit`, followed
  by `.pullback.inv`. `PullbackNormalization` is the existing simultaneous
  K-flat quotient/Roos representative normalization for that last identification.
  Each theorem explicitly asserts that this actual map is an isomorphism on
  complete inputs. Its naturality is that of the defined natural transformation.
- M,N are `sfIntegralConstructibleCategory l E Y`: exactly the recorded
  complete integral objects whose constructible reductions have one common
  finite cohomological interval. The `tensor` field of
  `PodCompletedTensorReindex` is the displayed ordinary-reindexing/completed-
  tensor isomorphism on those inputs. It uses `integralCompletedTensor`.
- `Canonical` is the equation identifying this isomorphism with the actual
  `canonicalIntegralPullbackTensor` under `podOrdinaryToCompleted`, on both
  the tensor and its two factors; it is not an existential unspecified arrow.
- `tower` is an isomorphism of entire strict tensor-reduction towers.
  `Generators` specifies each homogeneous total-tensor summand at each n,
  and `InverseGenerators` gives reverse relabelling on those same generators.
  `TowerNaturality` is an equality of whole tower maps; `Naturality` also
  quantifies over all morphisms of the input derived constructible objects.
- `podReindexProduct` is defined by `Pi.lift` of the actual product projections.
  `RoosBoundary` states its 1-s square. `RoosFst` and `RoosSnd` separately
  specify the two coordinates, including degree i-1 in the shifted coordinate.
  `LimitModel` and tensor `Model` compare the derived arrows with precisely
  these full Roos maps through the recorded K-injective-normalized limit model.
- Signed shifts use `PodSignedRoosShift.Laws`: the second coordinate carries
  `r.negOnePow`, while the unshifted coordinate uses the projection-defined
  product-shift map. `RoosShift` is the commuting square with reindexing.
  The tensor maps retain the degrees of each generator, hence the signed
  total differential and Koszul signs of the existing total tensor.
- Identity is `PodReindexFamily.Identity`, which states the whole-system
  equation for `(A.completion (𝟙 W)).reduction`, the total-limit equation for
  its `.limit`, and the tensor equation for `(A.tensor (𝟙 W)).tensor`. The
  ordinary identity is localized from `A.identity` and its section formula
  is fixed by `Relabelling`, using the actual site identity map.
- Composition is `PodReindexFamily.Composition`. It explicitly compares
  `(A.completion (h ≫ f)).reduction/.limit` and
  `(A.tensor (h ≫ f)).tensor` with the two successive selected maps. The
  coherent compositor is `integralComparisonSystemComposition`; the ordinary
  compositor is localized from `A.composition h f`, whose section formula is
  exactly the relabelling compositor `MorphismProperty.Over.mapComp`.
- Associativity, symmetry and units are `A.TensorConstraints l E f`. Each
  equation contains `(A.tensor f).tensor`, along with the actual completed
  associator, braiding or unitors. These are explicit own-map squares, not
  assertions that the preexisting canonical-arrow predicates hold.
- Coefficient transitions quantify over every finite L and embedding ι,
  including E=L and ι=id. `PodReindexCoefficientTransition.Laws` fixes the
  ordinary comparison on sheafified pure tensors, then states the whole-
  system reduction square using D.reduction/D'.reduction, the total-limit
  square using D.limit/D'.limit, and the tensor square using T.tensor/T'.tensor.
  `podScalarReduction` and `podScalarLimit` are actual scalar completion
  and coherent counit composites; no arbitrary scalar comparison is assumed.
- Signed shifts are `PodReindexSignedShifts`: `NatTrans.CommShift` for
  D.reduction and D.limit, the two limit/Roos representative squares, and
  the two explicit own T.tensor squares for shifting either factor.
  `PodTensorSignedShift.Generators` retains the unaltered first-factor
  generator and the second-factor sign (-1)^(pr). Its Model fixes both
  derived tensor shifts using the strict towers and the same signed Roos
  map. All integer shifts and arbitrary presentations of shifted inputs
  are quantified. The exact restriction/shift comparison is constructed
  by localizing the ordinary cochain comparison before the Roos map.
- `PodReindexSubstitution` uses a model C on Bool, with false=Y and true=X.
  Its two calculi, completion comparisons, Roos models and g-pullback
  realization are equal/heterogeneously equal to D's own data. Its tensor
  realizations are identified through qY,qX with the actual normalized
  strict-tower realizations; these isomorphisms themselves are fixed by
  qW followed by C.tensorRealization = pullbackTensorIntegralTensorModel. On every
  normalized system N the primitive pullback comparison, preceded by the
  defined ordinary-to-completed map on L_Y N, equals D.limit at N. Its
  tensor representative/canonical equations contain the same T. Comparison,
  substitution and structural laws then concern precisely this C. The
  returned unrelated `∀ W : Fin 3 → Scheme` copy is removed.
- F3 is repaired by `PodCompletionReindex.RestrictedGenerators`, now part
  of Laws. At every n,i,U it fixes D.restricted on every restricted section
  generator to restriction of the actual sequence-pullback adjunction-unit
  generator along `proEtaleIsoCommaArrow`. Negating D.restricted violates
  this formula; the former simultaneous sign change is no longer allowed.

Dependencies read and used:

- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus`,
  `CoefficientDerivedSystemCalculus`, its `reduction`, `adjunction`,
  `reductionEvaluation`, and the finite reduction models.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`, the
  generalized total-limit, K-injective and natural Roos interface.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `finiteFreeCompletedScalarComparison` and its identity-scalar augmentation
  normalization. The original completion unit is not replaced by a triangle.
- `Sheaf.Paper.CompletedPullbackTensorComparison`:
  `canonicalIntegralPullbackTensor`, with the normalized coherent-system model
  and the finite representative comparison imported from
  `Sheaf.Paper.FinitePullbackTensorComparison.canonicalFinitePullbackTensor`.
- `Sheaf.Paper.CompletedOperationTowerSubstitution`:
  `CompletedOperations.Models`, `ComparisonLaws`, `SubstitutionLaw`,
  `StructuralLaw`, and `completedOperationTowerSubstitution`.
- `Sheaf.Paper.DerivedPullbackTensorHom`:
  `constructibleIntegralPullback` and `constructibleIntegralTensor`, used by
  the canonical completed comparison; the underlying ambient operations are
  `integralDerivedPullback` and `integralCompletedTensor`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its
  full subcategory, with the same completeness and uniform-amplitude conditions.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and
  `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the existing finite
  quotients, constant maps, completed coefficients and quotient projections.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
  The scheme-properties dependency is a convention node, defining no substitute
  for scheme isomorphisms or invertibility.
- F2: the two former theorem dependencies used only for plain definitions
  (`lem-weil-isomorphism-derived-pullback-reduction-tower` and
  `lem-pur-derived-pullback-tensor-iso`) are replaced by definition owners
  `def-pod-isomorphism-reduction-reindexing` and
  `def-pod-integral-tensor-constraints`, as expressly requested in the return.
  Unit and unitors retain the already-landed owner
  `def-a1-common-stage-coefficient-unit`. The separate definition owner
  `def-pod-scalar-completion-tensor-comparisons` records the normalized scalar
  maps in `IntegralOperationsScalarComparisons`; the coherence theorem there
  is not a statement prerequisite. `def-weil-derived-complete` remains.
- `Sheaf.Paper.IntegralComparisonSequenceSystems`: the exact whole-system
  pullback, unit, composition and coefficient-transition comparisons.
  `Sheaf.Paper.IntegralComparisonRealizationModels`: the normalized scalar
  and Roos data. `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `integralComparisonScalarCounit`.
- Mathlib's `Functor.mapDerivedCategoryNatIso`, identity and composition
  localization isomorphisms, `Functor.CommShift`, `NatTrans.CommShift`, and
  `Adjunction.leftAdjointCommShift` supply the actual transports. The
  right-derived limit shift comes from the published right-derived-functor
  triangulated interface.
- The proof-only modules are imported for the assigned eight-step plan,
  including `PodReindexingHomResolutionModel`, independent-universe K-flat
  resolution, change of rings, total tensor, exact products, strict-limit
  comparison, well-defined integral operations and normalized reconstruction.

Edge cases checked: empty schemes (the residue-field hypotheses are then
vacuous, and the module categories and comparisons remain defined); zero
complexes and zero maps; g=id and h=id; first positive quotient n=0 (exponent
one); arbitrary integer tensor degrees and shifts, including negative and zero;
unbounded flat K-flat representatives; ambient incomplete K (no unit-inversion
claim); arbitrary ambient systems in the limit comparison. No exactness of
coefficient quotient extension is assumed. Site objects and morphisms retain
their distinct universes t+1 and t. The extra ambient theorem has independent
t and u, with coefficients in max u (t+1); the constructible tensor statement
uses the common ambient universe convention of the recorded intrinsic
constructible category, rather than changing that category or its coefficients.

Searches performed:

- msearch LeanSearch: "Inverse image along a scheme isomorphism preserves
  derived completion unit and completed tensor with quotient projection
  normalization". Eight results about ordinary scheme isomorphisms and
  restriction; no match for this normalized derived-system statement.
- msearch LeanFinder: "Exact reindexing along a scheme isomorphism commutes
  with derived completion unit strict quotient systems and completed tensor".
  Eight results, including `AdicCompletion.ofTensorProduct_naturality` and
  ordinary module adic completion; none gives this sheaf/derived-system theorem.
- msearch Loogle: `CategoryTheory.Equivalence, CategoryTheory.Adjunction`.
  Six results, including `Equivalence.toAdjunction`, generic adjunction transport
  and sheafification transport; none is the assigned statement.
- msearch grep in Mathlib CategoryTheory:
  `(reindex|Reindex).*(completion|Completion|tensor)|completion.*reindex`.
  Zero hits. Earlier logged queries in the sandbox were also read.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for reindex/completion
  and reindex/tensor terms; node-id search in `lean/WeilConjectures` gave no
  declaration. Related project modules are the existing resolution-Hom model,
  isomorphism reduction tower, ordinary scalar counit and native adic
  reindexing. They have different assertions or coefficient categories.
  The isomorphism-reduction and coherent-operation interfaces are reused here.
- Read the current blueprint source, dependency node records and the actual
  declaration signatures/docstrings, not just declaration names. The old
  CompactObject example is withdrawn; its recorded upstream module was read.


## Repair of F1, F2 and F3

The retained packet was inspected first. Its mandated initial dry run passed
(`OK (dry run): commit 9f82724b306`), but the copied coherence and free
restriction map identified in the return were still present. That packet was
not pushed. This delivery changes the Lean statement and definitions to repair
all three numbered findings; the mathematical node statement is unchanged.
The definitions were separated into modules to meet the original 60-second
per-file limit without raising it. No launcher or live source was edited.

## New nodes

- `def-pod-isomorphism-reduction-reindexing` owns the existing
  `IsomorphismReductionTower` coefficient comparison and ordinary/finite/
  cochain/derived reindexing definitions. Searches found those exact project
  definitions and no existing definition node; this is `existing: true`.
- `def-pod-integral-tensor-constraints` owns only the existing normalized
  integral associator and braiding in `DerivedPullbackTensorIso`. The
  separately recorded unit notion is reused through
  `def-a1-common-stage-coefficient-unit`, not duplicated.
- `def-pod-scalar-completion-tensor-comparisons` owns the existing uniquely
  normalized scalar completion map and ordinary-scalar/completed-tensor
  isomorphism; this is `existing: true`.
- `def-pod-completion-reindex-models` owns the ambient model and all
  quotient/projection/unit/counit/Roos/section-generator laws, plus the
  defined ordinary-to-completed map.
- `def-pod-completion-tensor-reindex-models` owns the strict tensor model,
  both tensor-generator rules and both naturality rules.
- `def-pod-completion-tensor-normalization` owns its exact Roos-model and
  canonical-comparison equations and their conjunction with the prior laws.
- `def-pod-completion-reindex-coherence` owns the single family, its
  section-normalized ordinary relabelling transports and its explicit
  identity, composition, associativity, symmetry and unit equations.
- `def-pod-completion-reindex-coefficient-transition` owns the scalar
  transport data and its actual reduction/limit/tensor squares.
- `def-pod-completion-reindex-shifts` owns the canonical shift instances,
  representative-normalized tensor shifts and own-map commuting equations.
- `def-pod-completion-reindex-substitution` owns the predicate fixing the
  completed-operation model to the selected D,T systems and primitives.

Each definition node follows blueprint Steps 1 and 5 and Stacks 03EL, 07A4,
0941. The recorded searches include LeanSearch (8 ordinary scheme/tensor
hits), LeanFinder (8 ordinary adic-completion and tensor hits), Loogle (12
generic shift hits) and Mathlib grep (0 matching reindexing/model names),
plus project/DAG/blueprint searches. The exact queries, result names and
digests are preserved in each new node's mathlib_searches. No existing
Mathlib or project definition packages the new own-map predicates.

## Second reading by Q51

This is the dispatched worker's separate self-reading; the brief prohibits
starting another agent. The maintainer's independent review remains separate.
Unlike the returned self-reading, this reading inspected the endpoints of
every coherence square and checked that each square contains the selected
D.reduction, D.limit or T.tensor. Identity uses g=id explicitly. Composition
uses h≫f and the normalized ordinary and coherent compositors. Scalar
transition includes E=L and ι=id, and its reduction arrow has the forward
scalar-reduction direction throughout. Both tensor factor shifts use the
same signed Roos maps and have their generator normalization. Substitution
is attached to D's two systems and to the actual g primitive.

The returned sign ambiguity was tested explicitly: a sign change of
D.restricted fails RestrictedGenerators, which evaluates the map on all
original local section generators. Its laws therefore pin the map before
LimitModel is used. No nonemptiness, boundedness, extra resolution choice,
or universe-equality assumption is added. Definitions contain real data;
only the two named item theorems have postponed proofs. Every new module has
one owning new node. Existing unit ownership was detected during this
second reading and reused rather than duplicated.

A final endpoint check caught that the slice tensor and the global Roos
tensor are canonically isomorphic presentations, not literally the same
chosen functor. The substitution predicate now retains qY and qX between
those presentations and fixes each by its full tensor-realization equation.
It no longer asks for heterogeneous equality of isomorphisms with distinct
source functors. These transports are uniquely determined by the displayed
equation, so they are not arbitrary extra maps or stronger assumptions.

Validation: scompile.py checked all eight delivered files in dependency order
at the unmodified 60-second, two-thread limit. Final library-path times were
35.3s ambient, 44.9s tensor models, 22.5s tensor normalization, 15.1s
coherence, 11.6s coefficient transition, 24.4s signed shifts, 3.5s substitution
and 3.9s item theorem. No error or warning remained. Earlier timeout drafts
were repaired by separating definitions and supplying actual shift transports;
no time limit was changed. The new definition edges have no dependency path
back to the item. The item differs from live only in lean and stmt_deps.

The first repaired-packet preflight reported exactly ten missing import_flags
keys (one per new definition node). Added import_flags: [] as required by the
current node schema and reran the prescribed dry run. No mathematics or Lean
signature changed for this metadata repair.
