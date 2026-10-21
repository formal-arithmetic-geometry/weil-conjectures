## Worker report

The module `Sheaf.Paper.PointTransformationCoefficientDescent` states
`WeilConjectures.PointTransformationDescent.coefficient_descent` with `sorry`.
Every other declaration is a real definition naming an existing canonical functor,
a composite of the specified comparisons, or a predicate spelling out a hypothesis
or conclusion. There are no other postponed proofs and no hollow data definitions.
The mathematical statement, proof and proof dependencies of the node are unchanged.

Hypothesis-by-hypothesis correspondence:

- The global tuple is `(D : FiniteFieldDatum.{u})`, with its prime, positive
  exponent, cardinality, finite base field and specified algebraic closure.
- The distinct coefficient prime is `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
- The chosen coefficient closure is `(Ω : Type u) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`.
- All finite intermediate fields are `F : AlgebraicallyClosedCoefficients.Index l Ω`.
  Their existing `Coefficient.{u} l Ω F` is the canonically equivalent small model
  of the actual intermediate field. The point-stage functor already transports
  this model back to `F.val` by `Shrink.algEquiv`; this is not a restriction to
  selected fields. Rings of integers, uniformizers and completions are those of
  the recorded coefficient and completed-integral-category declarations.
- `s` is literally `Spec (.of D.k)`, on the recorded small pro-etale site.
- The automorphism is `(g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]`.
  No Frobenius formula or base-field linearity of g is assumed.
- Integral objects are exactly `sfIntegralConstructibleCategory`, hence derived
  complete with the prescribed constructible reductions and uniform bounds.
- `integralPullback` calls the existing `constructibleIntegralPullback`;
  `rationalPullback` calls `rationalDerivedPullback`; `commonPullback` calls
  `commonStageDerivedPullback`. Their internal local typeclass value supplies
  residue-field invertibility from the existing
  `finiteFieldSpecCoefficientPrimeInvertible D l hl`. It adds no hypothesis.
- `integralSections` is the full-subcategory inclusion followed by the existing
  `pointCompletedDerivedSections`. This is the canonical ambient D(O_E) realization
  of the integral point-fiber sections, with the recorded actual coefficient action;
  it does not identify the completed sheaf with a discrete constant sheaf.
- `(η : IntegralFamily D l hl Ω g)` supplies arbitrary morphisms of integral
  sections to sections after completed pullback. Each member is a `NatTrans`,
  so it is natural for EVERY integral derived morphism, not just chain maps.
- `(hη : IntegralCompatible ... η)` quantifies over every inclusion F ≤ G,
  including equality, and every integral K. In Lean composition order it states
  `η_G(T K) ≫ F_G(alpha.inv) ≫ phi_(P K) = phi_K ≫ tensor.map(η_F(K))`.
  `integralAlpha` is `integralPullbackScalarComparison` and `integralPhi` is
  exactly `pointSectionsScalarExtensionIso`, with the recorded equivalence of
  intrinsic and legacy integral constructibility predicates supplied explicitly.
  Thus these are exactly the alpha and phi in the node's hypothesis. Their
  specified identity and tower identifications are inherited, not chosen anew.

Conclusion-by-conclusion correspondence:

- `∃ t : RationalFamily ...` supplies natural transformations between the actual
  `pointRationalFibre` and its composite with the actual rational pullback at
  EVERY finite intermediate field. These functors have the recorded pure-tensor
  action; a `NatTrans` quantifies over ALL rational morphisms. In particular this
  includes zero tensors, balanced tensors, and arbitrary finite sums of tensors.
- `RationalNormalized ... η t` states that each component is exactly η tensored
  with the fraction field, not just an unspecified rational transformation.
  It uses the canonical `pointRationalNormalization`, module carrier lift, and
  `pointModuleDerivedRationalization.map`. Conjugation by the normalization
  identifies the small target with the actual rationalized sections. `HEq` only
  accounts for the existing functors' propositionally specified object formulas.
- `RationalCompatible ... t` is equation (*) of proof step 3. Its `rationalB`
  is literally `pointRationalFibre.mapIso(alpha.symm)` followed by phi at P(K).
  Here alpha is `rationalPullbackScalarComparison` and phi is
  `pointRationalFibreScalarIso`. Both are uniquely normalized by precisely the
  integral comparisons used in the hypothesis; no arbitrary isomorphism occurs.
- `RepresentativeAssertions ... t` quantifies over arbitrary pairs A,B, any
  common field N, both inclusions, and every rational representative f. Its first
  clause is the SAME-FIELD equality `A_N(f) ≫ t_B^N = t_A^N ≫ B_N(f)` in D(N).
  `componentAt` is scalar extension of `stageComponent`, which is t transported
  through the exact existing Shrink coefficient equivalence.
- `fibreArrow` is exactly phi_source inverse, F_N(f), phi_target, in Lean order.
  `pullbackArrow` is exactly b_source inverse, H_N(f), b_target. `stageB` is
  F_N of the inverse of `commonStagePullbackComparison`, followed by the existing
  stage-phi at the pullback object. That comparison contains the precise recorded
  transition identifications, so this is b, not a competing realization.
- Its next clause treats EVERY N ≤ M, including equality: extending each of these
  two arrows by `pointTransport` agrees with the same formula at M applied to
  `(stageSystem ...).tr h f`. `pointTransport` is explicitly conjugation of the
  scalar-extended arrow by the existing tensor towers `pointFibreFdTensorTower`.
  Thus this clause identifies the images under further extension, including the
  associators, with the formulas for the transported representative. The first
  clause also holds at M for that representative, so it gives precisely the
  transported naturality equation there.
- Its last two clauses identify the actions of the SPECIFIED functors
  `pointQbarFibre` and `commonPullback ⋙ pointQbarFibre` on `mkHom N hA hB f`
  with `fibreClass` and `pullbackClass`, respectively. `pointClass` is the actual
  finite-stage cocone map with the prescribed `pointFdQbarStageComp` on both ends.
- `RepresentativeIndependent` states equality of BOTH class formulas for ANY two
  representatives with equal `mkHom` classes, even at different fields. This is
  exactly the recorded eventual-equality criterion, with no injectivity assumed.
  Together with same-stage naturality and the common natural transformation,
  equivalent representatives give the same naturality equation.
- The final `∃ τ : pointQbarFibre ⟶ commonPullback ⋙ pointQbarFibre` is an actual
  natural transformation with the required common-stage point target.
  `CommonNormalized ... t τ` fixes its component at every pair to the finite-stage
  class of the prescribed rational component. Its `HEq` inserts just the object
  equalities already fixed in the defining specifications of the two functors.

Dependency declarations used (module / names):

- `Sheaf.Paper.FiniteFieldFiber` / `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (and its imported
  `CoefficientExtension`) / `Padic.finite_coefficientExtensionRing`, the recorded
  integer rings, uniformizers and finite coefficient rings.
- `def-weil-scheme-morphism-properties` is a convention record without a module;
  schemes, morphisms, `Spec` and `IsIso` use the imported Mathlib declarations.
- `Mathlib.AlgebraicGeometry.Sites.Proetale` / `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.SfIntegralConstructible` / `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.DerivedPullbackTensorHom` / `constructibleIntegralPullback`,
  `rationalDerivedPullback`, `integralPullbackScalarComparison`,
  `rationalPullbackScalarComparison`, `commonStageDerivedPullback`,
  `commonStagePullbackObject`, `commonStagePullbackComparison`.
- `Sheaf.Paper.FiniteCoefficientPoint` / `pointRationalFibre`,
  `pointRationalNormalization`, `pointRationalFibreScalarIso`, `pointStageFibre`,
  `pointStageFibreScalarIso`, `pointFibreFdTensorTower`, `pointQbarFibreObj`,
  `pointQbarFibre` and their recorded defining specifications.
- `Sheaf.Paper.IsomorphismDerivedPullback` /
  `isomorphismIntegralDerivedPullback_termwise` (proof-plan import).
- `Sheaf.Paper.IntegralScalarExtensionUniverses` /
  `integralScalarExtensionOfUniverses`, retaining the original canonical
  `integralScalarExtension` used by the restricted scalar functor.
- `Sheaf.Paper.IntegralOperationsScalarComparisons` /
  `scalarPullbackCompleted` under the canonical restricted alpha, and the recorded
  naturality, identity and tower assertions.
- `Sheaf.Paper.PointSectionsScalarExtension` / `pointCompletedDerivedSections`,
  `pointSectionsScalarExtensionIso`, `pointIntegralModuleDerivedTensor`,
  `pointModuleDerivedRationalization`, `pointIntegralConstructible_iff`,
  `pointSectionsScalarExtension`.
- `Sheaf.Paper.SfRationalizationKaroubi` / `sfRationalConstructibleCategory`,
  `sfRationalScalarExtension`, `sfRationalConstructibleLocalization`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` /
  `generalAlgebraicallyClosedConstructibleCategory`, `stageSystem`,
  `StageSystem.PairCategory.mkHom`, `StageSystem.tr`.
- `Sheaf.Paper.PointFdQbarCategory` / `DerivedCategory.PointFdQbar`,
  `pointFdQbarStage`, `pointFdQbarStageComp`, with the actual scalar functor
  `DerivedCategory.pointFdScalarExtension`.
- Added existing node `def-sf-point-fibre-tensor-system`, module
  `Sheaf.Paper.PointFibreDerivedTensorBasic`, solely for its already recorded
  `finiteFieldSpecCoefficientPrimeInvertible`. This supplies a necessary proof
  parameter for the existing operations; it defines no new notion and imposes no
  extra invertibility assumption. No dependency record is changed.

Edge cases checked before and after drafting: g = identity; any other scheme
isomorphism; η identically zero and arbitrary noninvertible components; zero and
integral torsion objects (including those rationalizing to zero); zero, pure,
balanced and sums of rational morphism tensors; equal coefficient fields F = G;
common stage equal to either endpoint; M = N in further extension; representatives
at unrelated fields that become equal at a later field. No component is assumed
invertible. No transition-map injectivity or special formula for η is assumed.
The chosen universe contains both the global field datum and the coefficient
closure, as in the recorded four-fiber interface; the pro-etale site retains its
original distinct object/morphism sizes. No size equality is imposed on that site.

Searches made for an existing exact statement:

1. `msearch.py ... leanfinder` query: "Scalar compatible integral natural
   transformations descend to rational morphism tensors and common finite
   coefficient field representatives". Eight hits: `IsIntegral.tmul`,
   `Algebra.TensorProduct.instCompatibleSMulRat`, polynomial-law tensor lifting
   results, and `Algebra.IsIntegral.tensorProduct`. None states this assertion.
2. `msearch.py ... loogle '"natTransExtension"'`: six localization hits, including
   `CategoryTheory.Localization.Construction.natTransExtension` and its app,
   whiskering and composition lemmas. These extend transformations along a
   localization but do not identify the supplied completed integral comparisons
   or the two normalized common-field actions, so none is an exact match.
3. `msearch.py ... grep '(NatTrans|natTrans).*(rationaliz|commonStage)|commonStage.*[Nn]atur'`:
   zero hits in Mathlib.
4. `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for the item id and rational
   or common-stage natural-transformation patterns: only unrelated approximation,
   Artin--Schreier and coefficient-module results; no exact declaration. Read
   the source modules recorded by all statement dependencies, including the full
   point-fiber normalization and representative specifications. The example
   `CompactObject.lean` is withdrawn in this snapshot; its node record was read.
5. `msearch.py ... leansearch` query: "A scalar compatible integral natural
   transformation of point sections descends to rationalized Hom tensors and
   common finite coefficient fields". Eight hits: compatible module-sheaf scalar
   families, `NatTrans.app_smul`, `NatTrans.appLinearMap`, a tensor scalar instance,
   the module extension/restriction adjunction, `PresheafOfModules.unitHomEquiv`,
   `NatTrans.app_units_zsmul`, and sheaf Hom integer scalar action. None gives
   the specified integral-to-rational and common-stage transformation descent.
6. Read Deligne's PDF printed pp. 150--151, (1.1.3) and (1.1.7), using pdftotext
   pages 15--16. The former gives rational Hom scalar extension and coefficient
   colimits; the latter gives the point-transport context. As the node explicitly
   records, the normalized pro-etale descent argument is the agent-written DAG
   argument, not a theorem attributed to Deligne.

No statement dispute, statement correction, new node, or dependency repair.
The module was compiled using only the prescribed `scompile.py` wrapper. The
initial namespace-resolution error was repaired by qualifying the opened coefficient
namespace; the initial docstring line-length warning was repaired by wrapping prose.
Final compilation and delivery preflight results are recorded below.

## Second reading by Q120

The dispatcher assigned this worker directly and explicitly prohibited starting
other agents. This section records the worker's final rereading, not an invented
independent reviewer; the maintainer's independent review remains required.
I reopened the node and checked the integral hypothesis against `IntegralCompatible`
(right-to-left mathematical composition versus left-to-right Lean composition),
verified the inverse direction in `rationalB` and `stageB`, checked both representative
formulas, and checked that the same-field equation involves arbitrary rational f.
I also checked `RationalNormalized` against the exact size-normalization maps and
`CommonNormalized` against the unchanged finite-stage component class. The final
rereading added explicit tensor-tower transport of BOTH actions to the extension
clause: merely applying tensor to an equality would not itself identify it with
the equation for the transported source representative. Identity fields, zero
transformations and eventual equality of distinct representatives remain included.

Final validation: the prescribed `deliver2.py --no-push` completed with
`OK (dry run): commit 00da3f22a45 passes the preflight and compiles; nothing pushed`.
Both sandbox and library single-file compilation are clean. The node's `lean.statement`
is verbatim from the theorem signature, no Lean line exceeds 100 characters, and the
sole `sorry` is the requested theorem. The added existing dependency has no dependency
path back to the item. Final delivery uses the unchanged authorized wrapper.
