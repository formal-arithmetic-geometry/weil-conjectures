## Worker report

The delivery states `WeilConjectures.normalizedScalarComparisonRealization` in
`Sheaf.Paper.NormalizedScalarComparisonRealization`. Its only postponed proof is the
main theorem, with the complete fifteen-step DAG proof in its docstring. Every helper
has actual data or is an explicitly defined predicate/structure. Nothing is proved here.
The item statement, dependencies and proof are unchanged.

The blueprint source was read at main-20261015, sec-proetale-coefficients /
sk-def-sf-operations / def-weil-derived-pullback-tensor-hom.md. It defines the integral
operations by compatible finite reductions and derived inverse limit. The item's
reviewed agent refinement supplies the normalization and the two equations. The Lean
uses the actual strict sequence site and ordinary derived category throughout.

Hypotheses and objects, matched individually:

- A prime ell: the explicitly declared section variables `(l : ℕ) [Fact l.Prime]`.
- Finite E and L over Q_l: `(E L : Type u)` with their separate `Field`,
  `Algebra ℚ_[l]` and `FiniteDimensional ℚ_[l]` instances.
- The inclusion E into L: `ι : E →ₐ[ℚ_[l]] L`, the existing coefficient embedding
  interface. A field algebra homomorphism is injective; no quotient map is assumed
  injective or flat.
- Chosen valuation rings, uniformizers and positive coefficient exponents: those of
  `Padic.coefficientExtensionRing` and the recorded integral coefficient sheaves.
  Natural index n means exponent n+1, so the first level is included.
- The schemes and morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Ell invertible on both schemes: `_hX : IsUnit (l : Γ(X, ⊤))` and `_hY` on Y.
  This is the scheme-theoretic invertibility of the integer ell, with no auxiliary
  global finite-field datum or restriction on the characteristic elsewhere.
- Completed rings and their limit projections: the unchanged
  `completedIntegralCommRingSheafUnrestricted` and
  `completedIntegralCommRingProjectionUnrestricted` used by all dependency interfaces.
- The homomorphisms i_n and actual quotient transitions: the recorded
  `integralScalarQuotientSheafMap`, `integralComparisonSequenceScalarMap`,
  `coefficientSequenceTransition`, and `unrestrictedIntegralFiniteComplex`.
- Coherent reduction, total limit and counit: the explicitly declared calculi
  `EX EY LX LY : CoefficientDerivedSystemCalculus ...`; their `.reduction`,
  `.adjunction.counit` and the actual `coefficientSequenceLimit`. These are the
  recorded calculus data quantified universally, rather than hypotheses supplying
  any of the realizations asserted by this item.
- Normalization: `IsNormalizedCoefficientSequence`, the actual transition-adjoint
  condition from the recorded system calculus. No private normalization predicate
  replaces it.
- Integral inputs M,N in D^b_c: the binders in the representative-closure and equation
  predicates use `sfIntegralConstructibleCategory l E Y`. Thus completeness,
  constructibility of every reduction and a single finite support interval are all
  retained. `.property.1` supplies precisely the existing completeness hypothesis.
- Flat-term K-flat representatives: `integralOperationsGoodComplex`, with its actual
  `IsKFlatIndependentCoefficients` and `IsFlatOnSite` conjuncts. The representative
  closure explicitly requires isomorphisms from their images under Q to M and N.
  The helpers allow independent site/coefficient universes t,u; the final theorem
  uses the common ambient universe of the recorded integral constructible category.
  The small pro-etale site still has objects in u+1 and morphisms in u, never equalized.

Conclusion clauses, matched individually:

1. All iterated finite representatives remain flat-term K-flat:
   `NormalizedScalarRepresentativeClosure`. The inductive
   `NormalizedScalarGenerated` starts from P_n and Q_n and closes under the actual
   E-to-L scalar extension at X or Y, finite E/L pullback and signed total tensor
   at each of the four locations. Its conclusion is the conjunction of the existing
   K-flat predicate and `SemilinearSections.flatTerms`. There is no bound on the
   length of the finite expression, on the complexes or on their cochain degrees.
2. The balanced associations with insertion-of-one inverse and every transition:
   `NormalizedScalarQuotientAssociations` uses
   `CoefficientExtensionReductionData` for the two sites and their actual scalar
   systems. Its association, strict-transition, evaluation and completion-projection
   fields fix exactly `(x tensor a) tensor b -> x tensor i_n(a)b`; they give inverse
   isomorphisms and normalized quotient systems for the specified scalar functor.
   This reuses the dependency's statement without a duplicate association definition.
3. The finite pullback/tensor/scalar systems are normalized:
   `NormalizedScalarSystemPreservation` spells out each preservation assertion for
   the actual whole-system functors and tensors. The calculi already assert that
   reductions of every ambient integral input are normalized, including completed
   operation inputs. Therefore this covers the intermediate systems in both equations.
4. Existence of representative-normalized realizations:
   the existential `D : NormalizedScalarOperationModels ...` supplies `pullE`, `pullL`,
   `scalarX`, `scalarY`, `tensorE`, `tensorL` and the four `roos...` models. Pullback and
   scalar reuse `IntegralComparisonPullbackModel` and `IntegralComparisonScalarModel`.
   `NormalizedScalarTensorRealization` supplies the tensor counterpart on the actual
   `integralCompletedTensor`. Its normalization tests every simultaneous quotient
   presentation C,D of every P,Q, uses signed pure-tensor generators, and requires
   equality with `integralCompletedTensorComparison` after the fixed total-limit/Roos
   bridge. The existing Roos models specify the ordinary limit cone on K-injectives
   with zero shifted coordinate. These are functor isomorphisms, with maps fixed.
5. The maps r_F,r_T,r_S are exactly reduction of those realizations followed by the
   actual coherent counit: the three `normalizedScalar...Reduction` definitions are
   precisely these two-term composites. `NormalizedScalarReductionsInvertible` asserts
   their invertibility on the reductions of all the displayed ambient inputs.
6. Unique derived-system tensor scalar localization: `D.sigma`,
   `D.sigma_normalized`, `D.sigma_unique`. The normalization predicate requires an
   ordinary natural chain isomorphism fixed on every signed total tensor generator,
   at every coefficient-system section, with arbitrary scalar b. Its derived square
   includes the universal change-of-rings counits and the fixed K-flat tensor model
   isomorphisms. It is imposed before evaluation, on all flat-term K-flat system
   representatives. The pullback localization is the already uniquely normalized
   `integralComparisonSystemScalarPullback`, not a fresh arbitrary isomorphism.
7. The first displayed equation is the first conjunct of
   `NormalizedScalarReductionEquations`. In Lean's composition order its left side is
   `LX.reduction.map a_F.hom ≫ r_F,L ≫ F_L.map r_S,Y`; its right side is
   `r_S,X ≫ S_X.map r_F,E ≫ kappa.hom.app (EY.reduction.obj M.obj)`.
8. The second displayed equation is the second conjunct of that predicate. Its left
   side is `LY.reduction.map a_T.hom ≫ r_T,L ≫ T_L.map (r_S,r_S)`; its right side is
   `r_S ≫ S.map r_T,E ≫ D.sigma.hom.app (R_E M,R_E N)`.
   The completed arrows are exactly the dependency's `scalarPullbackCompleted` and
   `scalarTensorCompleted`. Completeness of their operation inputs is existentially
   concluded with the equations, not assumed as an added hypothesis.
9. Evaluations and all quotient transitions are retained because every arrow in both
   equations belongs to `coefficientSequenceDerived`, the ordinary derived category
   of entire strict module systems; there is no argument from equality of evaluations.
10. The consequent total-limit descriptions are written separately as
    `NormalizedScalarLimitEquations`. In each case the equation is
    `a_H ≫ beta_B = beta_A ≫ coefficientSequenceLimit.map alpha_H`, with beta_A and
    beta_B expanded using the stated realizations and reduction maps. This is exactly
    the asserted conjugation by normalized source and target coordinates.
11. Naturality in inputs is additionally explicit in
    `NormalizedScalarComparisonNaturality`, for arbitrary integral input morphisms
    and both tensor variables. Independence from resolutions is expressed by all
    the universal representative-normalization tests, their isomorphisms in the
    ordinary derived categories and uniqueness of the specified localization; it
    introduces no chosen resolution into a completed comparison's signature.
12. No flatness assumption on finite scalar maps, and no operation/inverse-limit
    interchange hypothesis, occurs anywhere in the theorem.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, importing the actual coefficient rings.
- `def-weil-scheme-morphism-properties` is the recorded convention node, not a
  declaration to duplicate; schemes, morphisms and global invertibility use the
  existing AlgebraicGeometry interfaces.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`,
  `integralConstantToCompletionOfUniverses` and its actual coefficient cone.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`,
  `integralScalarExtensionOfUniverses`, `integralScalarExtensionComparisonOfUniverses`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`,
  `CoefficientDerivedSystemCalculus`, `CoefficientReductionPresentation`,
  `CoefficientTensorModels.iso`, and `coefficientDerivedSystemEvaluationCalculus`.
- `Sheaf.Paper.NormalizedDVRTower`, `NormalizedDVRTower`, including its adjoint
  normalization and coherent tower fields; the whole-system formulation used here
  is its existing `IsNormalizedCoefficientSequence` incarnation in the calculus.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`, `IntegralOnSlice.completedTensor`,
  retaining the global completed tensor and pullback from `IntegralDerivedOperations`;
  the latter's exact `integralCompletedTensorComparison` is used in normalization.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`, `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Paper.SfIntegralConstructible`, `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.CoefficientExtensionReductionModel`, `CoefficientExtensionSystems`,
  `CoefficientExtensionReductionData`, `coefficientExtensionReductionModel`.
- `Sheaf.Paper.IntegralComparisonRealizationModels`, `IntegralComparisonRoosModel`,
  `IntegralComparisonPullbackModel`, `IntegralComparisonScalarModel`,
  `integralComparisonRoosBridge`, and their representative normalizations.
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`,
  `CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`, `scalarPullbackCompleted`,
  `scalarTensorCompleted`, retaining their normalized ordinary comparisons.
- `Sheaf.Paper.SemilinearDerivedSections`,
  `SemilinearSections.SemilinearDerivedSectionsData`, `semilinearDerivedSections`;
  its existing representative helpers `flatTerms` and scalar model interfaces
  occur directly. Whole-system pullback and kappa use the already defined
  `IntegralComparisonSequenceSystems` declarations, reexported by realization models.

All already recorded proof-dependency modules are explicitly imported (public imports
for the interfaces used by statements, ordinary imports for proof infrastructure).
No import is possible yet for the three proof nodes without a recorded module:
`lem-pur-completed-primitive-counit-comparison`,
`lem-pur-strict-coefficient-comparison-calculus`, and
`lem-weil-pbc-localization-universal-property`. They are proof prerequisites, not
missing notions needed to type this statement; none is silently replaced by an axiom.
No import cycle was introduced.

Searches for an exact existing statement and duplicate helper names:

- `msearch.py`, LeanFinder, query "Normalized realization of scalar comparisons on
  quotient systems of sheaves with coherent reduction and derived inverse limit":
  eight hits on module presentations, sheafification and normalization diagrams;
  none is this comparison or its strict-system equations.
- `msearch.py`, Loogle, query `NatIso, Adjunction.counit`: zero hits, unknown identifier
  `NatIso`. This result was not treated as a successful semantic match.
- `msearch.py`, Mathlib grep, query `normalized.*scalar|scalar.*realization`, restricted
  to CategoryTheory: zero hits.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf`, query
  `normalizedScalar|NormalizedScalar|scalarComparisonRealization|ScalarComparisonRealization|normalized-scalar-comparison-realization`:
  unrelated scalar boundary/composition and matrix transport helpers; no exact statement.
- `rg` over both source trees and the upstream declaration-name index for
  `normalizedScalarComparisonRealization|NormalizedScalarOperationModels|NormalizedScalarGenerated|IsNormalizedScalarTensorLocalization`:
  no existing declarations. The item id has no source attachment elsewhere.
- Direct inspection found the existing pullback and scalar realization models and
  normalized system kappa, which are reused. No existing tensor realization says
  this item's combined statement; only its missing counterpart and owning helpers
  are introduced. There are no new DAG nodes or dependency-interface repairs.

Edge cases checked before finalizing:

- Zero inputs and empty schemes impose no nonzero object or nonempty site condition.
- Positive exponent 1 is index 0; all indices remain present. Identity transitions
  are retained by `CoefficientReductionPresentation` and the system category.
- E=L and the identity scheme morphism are allowed. No strict field inclusion or
  nonidentity-map hypothesis excludes these cases.
- Ramified extensions are allowed, including noninjective and nonflat i_n. All finite
  scalar operations are derived, tested on K-flat representatives; no ring-flatness
  premise has been inserted.
- Arbitrary negative degrees, unbounded resolutions, arbitrary finite iterates and
  the signed direct-sum total tensor are retained. Bounded constructibility is imposed
  only on the stated integral inputs, not on resolution terms.
- Tensor normalization uses all system sections and every simultaneous quotient
  presentation, not unrelated finite evaluation equalities. Consequently signs,
  transitions and the actual maps survive the limit descriptions.

Validation: the prescribed scompile.py wrapper compiled the module separately against
the live published library, both its sandbox and library probes, cleanly within the
60-second limit. Final dry-run and delivery results follow from deliver2.py.
No STATEMENT-DISPUTED finding or statement correction.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
