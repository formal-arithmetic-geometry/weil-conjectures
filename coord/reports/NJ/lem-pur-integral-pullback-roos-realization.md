## Worker report

Record the exact existing declaration
`WeilConjectures.pullbackTensorIntegralPullbackModel_existsUnique` in
`Sheaf.Paper.CompletedPullbackTowerRealizations`, source line 241. No new module,
new definition, dependency repair, statement correction or proof is delivered.
The existing theorem already has a proof; this delivery only attaches its statement
under the one-definition-per-notion rule. The node's candidate extraction module
is a future possibility, not a requirement to duplicate the theorem.

I read the node's complete statement and proof, its statement dependencies and their
Lean records, the relevant source signatures and docstrings, the existing theorem
and the definitions it uses. No released repair note exists for this item.

Hypothesis-by-hypothesis and clause-by-clause match:

- The section parameters are `(l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. These give precisely the
  prime and finite coefficient field extension. Its valuation ring, uniformizer,
  quotient rings and quotient transitions are the existing `Padic.coefficientExtension*`
  constructions imported through the dependencies. No uniformizer is reselected.
- `{X Y : Scheme.{u}} (f : X ⟶ Y)` quantifies over the schemes and arbitrary scheme
  morphism in the node. The node explicitly uses this universe u presentation;
  the small pro-etale sequence site has object universe u+1 and morphism universe u.
  No new equation between distinct site object and morphism universes is imposed.
- `coefficientSequenceTopology`, `coefficientSequenceCommRingSheaf`,
  `coefficientSequenceModules`, and `coefficientSequenceRestriction` give the actual
  ringed sequence site, strict quotient-semilinear systems and simultaneous exact
  scalar restriction U. `coefficientSequenceEvaluation` is e_n. Its n is the actual
  quotient exponent n+1, including n=0. Completed module coefficients are
  `completedIntegralCommRingSheafUnrestricted`, used by `integralTowerModules`.
- `DerivedCategory`, `DerivedCategory.Q`, and the cochain-complex functors use all
  integer degrees and ordinary unbounded derived categories, not a complete or
  bounded subcategory. `coefficientSequenceLimit` is Rlim after exact restriction.
  `(pullbackTensorCalculus l E W).reduction` and `.adjunction` are the fixed
  derived reduction and adjunction from the recorded evaluation calculus.
- `integralOperationsGoodComplex` is exactly the conjunction of
  `CochainComplex.IsKFlatIndependentCoefficients` and flatness in every degree.
  The K-flat predicate quantifies over all acyclic complexes and uses
  `CochainComplex.mapBifunctor` with the sheaf tensor, hence direct-sum total tensor.
  `.FullSubcategory` stores these properties; it adds no property of the input
  derived object. No boundedness, constructibility, derived completeness or
  invertibility of l occurs in the theorem or these binders.
- `pullbackTensorOrdinaryLimit`, `pullbackTensorOrdinaryReduction` and
  `pullbackTensorOrdinaryAdjunction` are L^0, r and their chosen adjunction/unit.
  `pullbackTensorLimitUnit` inserts the exact restriction/localization comparison.
  `pullbackTensorReductionModel` is m, selected from the unique natural isomorphism
  whose transpose is Q of the ordinary adjunction unit followed by that limit unit.
- `pullbackTensorSequenceBase`, `pullbackTensorSequenceRing`,
  `pullbackTensorSequenceDirect`, `pullbackTensorSequenceInverse`,
  `pullbackTensorSequenceAdjunction` and `pullbackTensorSequenceDerived` supply b_f,
  its constant-section coefficient map, the specified direct/inverse adjunction
  and its exact derived inverse image. The finite evaluation comparisons are
  `pullbackTensorReductionEvaluation` (a) and
  `pullbackTensorSequenceInverseEvaluation` (v), with the prescribed unit/mate
  normalizations in their defining unique-existence statements.
- `integralOperationsRoosFunctor` is the actual signed mapping cocone of 1-s on
  the product of the reordered strict tower. Its map uses the product of the
  tower components on both coordinates. `pullbackTensorRoosUnit` is the canonical
  mapping-cocone lift with ordinary limit projections and zero second component.
  `pullbackTensorRoosModel` (rho) is fixed on K-injectives by exactly the
  `rightDerivedFunctorObjQIso` followed by Q of that lift, on all tower complexes.
- `integralOperationsPullbackTowerFunctor` is B_f^0 with its quotient transitions
  and its action on arbitrary chain maps. `pullbackTensorRestrictedTower` performs
  restriction and reordering. `pullbackTensorPullbackTower` is c; its defining
  theorem fixes its nth component to `pullbackTensorPullbackTowerLevel`, whose
  factors are the reordering/restriction identification, inverse v, then the
  finite inverse a under pullback. These are strict tower maps.
- `pullbackTensorReferencePullback` is precisely reduction followed by
  `pullbackTensorSequenceDerived` followed by `coefficientSequenceLimit`, namely
  F_ref. `pullbackTensorReferencePullbackModel` is precisely mu: first apply the
  limit and inverse image to m, then insert exact inverse-image factorization,
  then `pullbackTensorLimitRoos`, then Q applied to the full Roos image of c.
  `pullbackTensorLimitRoos` itself inserts exact restriction factorization and rho.
  Thus mu includes both cone coordinates and all strict quotient transitions;
  it is not characterized merely by finite derived projections.
- `integralDerivedPullback` is the actual completed pullback, the functor field
  of `integralPullbackDescent`; `integralDerivedPullbackComparison` is epsilon,
  its comparison field with `integralOperationsPullbackOnGood` = Q H B_f^0.
- `∃! e : integralDerivedPullback l E f ≅ pullbackTensorReferencePullback l E f`
  is existence and uniqueness of the natural isomorphism on the entire derived
  category. Uniqueness is restricted only by the following normalization predicate.
- `∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory` is exactly every
  flat-term K-flat representative. The equation
  `e.app (DerivedCategory.Q.obj P.obj) =
  (integralDerivedPullbackComparison l E f).app P ≪≫
  (pullbackTensorReferencePullbackModel l E f P).symm`
  is epsilon followed by inverse mu, hence mu^{-1} composed with epsilon in the
  node's conventional right-to-left notation. It is equality of whole isomorphisms.

Dependency declarations read and used (all names beginning coefficient*, integral*
and pullbackTensor* below are in namespace WeilConjectures):

- `def-weil-l-adic-coefficient-extension`:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, publicly retaining
  `Sheaf.NumberTheory.Padics.CoefficientExtension` and its actual coefficient data.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `.Hom`.
- `def-coef-ringed-sequence-site`: `Sheaf.Paper.CoefficientRingedSequenceSite`,
  `coefficientSequenceCommRingSheaf`, topology, modules, evaluation, restriction,
  derived categories and limit.
- `lem-coef-derived-system-evaluation-calculus`:
  `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`,
  `coefficientDerivedSystemEvaluationCalculus`; the core's
  `pullbackTensorCalculus` selects its specified calculus.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `def-pc-tensor-complex-sheaves`: `Mathlib.Algebra.Homology.BifunctorShift`,
  `CochainComplex.mapBifunctor`, with the existing sheaf tensor.
- `def-trf-integral-comparison-sequence-systems`:
  `Sheaf.Paper.IntegralComparisonSequenceSystems`,
  `integralComparisonDerivedSequencePullback` and its ordinary coefficient-site
  direct/inverse image constructions; the core specializes the same adjoint
  construction and pins its evaluation comparison to the actual adjunctions.
- `def-sf-strict-roos-functor`: `Sheaf.Paper.IntegralOperationsWellDefined`,
  `integralOperationsRoosFunctor`.
- `def-pur-integral-derived-operations`: its recorded module
  `Sheaf.Paper.IntegralDerivedOperationsOnSlices` publicly retains
  `Sheaf.Paper.IntegralDerivedOperations`. The latter's `integralDerivedPullback`
  and `integralDerivedPullbackComparison` are the global operations used here;
  the slice-only `IntegralOnSlice.completedTensor` is irrelevant to this pullback
  theorem. No replacement slice pullback or duplicate operation is introduced.
- `def-trf-integral-pullback-descent-model`:
  `Sheaf.Paper.IntegralDerivedOperations`, `IntegralPullbackDescent`,
  `integralPullbackDescent`, `integralDerivedPullback`,
  `integralDerivedPullbackComparison`; its universal field is the uniqueness used.
- `def-a1-integral-finite-pullback-tower`:
  `Sheaf.Paper.IntegralOperationsWellDefined`,
  `integralOperationsPullbackTowerFunctor`, with its recorded levels and transitions.
- `def-pur-completed-pullback-tower-core`:
  `Sheaf.Paper.CompletedPullbackTowerCore`, `pullbackTensorFiniteAdjunction`
  and the core comparisons enumerated above, especially
  `pullbackTensorReductionModel`, `pullbackTensorRoosModel`,
  `pullbackTensorPullbackTower`.

The existing theorem's proof has exactly the node's assembly: componentwise
naturality of the strict tower comparison, whiskered natural factorization
comparisons giving mu, then
`CategoryTheory.normalizedDescentComponents_existsUnique` from
`Sheaf.Paper.IntegralPullbackDescentComponents` applied to the universal field
of `integralPullbackDescent`. That proof dependency is already imported by the
existing module. Nothing is proved anew in this delivery.

Edge cases checked by reading the signatures and definitions: n=0 is exponent 1,
not the zero quotient; all integer cochain degrees are allowed; zero complexes
and empty schemes are not excluded; arbitrary scheme morphisms include identities;
l may equal the scheme's characteristic; arbitrary ambient objects need not be
complete. The statement does not assert finite projections detect derived maps.
There is no new independent-universe assumption or nonempty-site assumption.
No node fault or STATEMENT-DISPUTED issue was found.

Sources read: the named latest blueprint coefficient-twist page (finite-reduction
compatibility); Stacks `sites-cohomology.tex`, label `lemma-derived-limit-is-ok`
(Tag 0941), and `derived.tex`, label `definition-derived-limit` (Tag 08TC).
These give the derived-limit models; the project's normalized descent is the
additional explicit normalization, as the node's source/proof already says.

Searches made with msearch.py NJ lem-pur-integral-pullback-roos-realization:

- leanfinder: "Completed integral pullback is uniquely naturally isomorphic to
  coherent reduction pullback and derived limit with the full Roos comparison on
  flat K-flat representatives". Eight ordinary sheaf pullback/composition hits,
  including `SheafOfModules.freeFunctorCompPullbackIso`; none is this full theorem.
- loogle: "CategoryTheory.Localization.liftNatIso,
  CategoryTheory.Functor.leftDerivedUnique". Zero hits.
- grep (CategoryTheory): "liftNatIso|normalizedDescentComponents|
  pullbackTensorIntegralPullbackModel". Twenty-five general localization hits,
  including `Localization.liftNatIso`, not the project-specific theorem.
- leansearch: "There is a unique natural isomorphism from completed integral
  pullback to coherent reduction inverse image and derived inverse limit with
  prescribed Roos components". Eight constituent functor/pullback/limit results;
  no full normalized completed-pullback theorem.
- rg in lean/WeilConjectures and lean/Sheaf for
  `pullbackTensorIntegralPullbackModel_existsUnique`,
  `pullbackTensorReferencePullbackModel` and
  `normalizedDescentComponents_existsUnique`: exact theorem at
  CompletedPullbackTowerRealizations.lean:241 and its users; the independent
  descent-components lemma at IntegralPullbackDescentComponents.lean:34.
- rg in lean/WeilConjectures for this DAG id: no hits. The exact match is already
  in lean/Sheaf, so it is reused with existing=true and no extraction module.

Validation: the required deliver2.py dry run compiles a generated server #check
probe for the existing declaration through scompile.py, then performs server
preflight. No delivered Lean file needs separate compilation.

## Second reading by NJ

Independent second reading (maintainer reviewer NT-cc, 2026-10-27); it replaces the
in-session self-check delivered at 0aa571e4, which was not an independent reading (H11).
The record is `existing: true`; the Lean (live `Sheaf.Paper.CompletedPullbackTowerRealizations`,
line 241, byte-identical in the published tree) was read against the node statement, its
three proof steps and the declarations of every statement dependency. Nothing is changed.

Node clauses and their Lean rendering (`pullbackTensorIntegralPullbackModel_existsUnique`):
- prime l, finite E/Q_l, O_E, uniformizer: section variables `(l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`; quotient
  rings from def-weil-l-adic-coefficient-extension. Exact.
- schemes in universe u, morphism f : X → Y: `{X Y : Scheme.{u}} (f : X ⟶ Y)`. E shares
  universe u with the schemes; this is the convention of the landed stmt_dep
  def-pur-completed-pullback-tower-core (every core def has `E : Type u`, `Scheme.{u}`),
  so it is forced by the cited interface, and the DAG has no citer of this item. Advisory only.
- A_W, S_W, e_{W,n}, U_W, L_W = Rlim∘D(U_W): `coefficientSequenceLimit` =
  `coefficientSequenceDerivedRestriction ⋙ coefficientConstantTowerLimit` (rightDerivedFunctor
  of lim); `CoefficientDerivedSystemReductionModel.adjunction : reduction ⊣ coefficientSequenceLimit`,
  so R_W ⊣ L_W is the fixed calculus adjunction (`pullbackTensorCalculus = (...Calculus).choose`). Exact.
- good complexes: `integralOperationsGoodComplex` = `IsKFlatIndependentCoefficients` ∧ termwise
  `IsFlatOnSite`, no boundedness. Exact.
- m_W: `pullbackTensorReductionModel`, unique e whose `adjunction.homEquiv` transpose is
  `Q.map (ordinary unit) ≫ pullbackTensorLimitUnit`, i.e. λ ∘ q(η^0). Exact.
- ρ_W: `pullbackTensorRoosModel`, fixed on K-injective I by `rightDerivedFunctorObjQIso.hom ≫
  Q.map (pullbackTensorRoosUnit I)`, the mapping-cocone lift of `Pi.lift (lim.π)` with zero
  second coordinate. Exact.
- H_W: `integralOperationsRoosFunctor` (mappingCocone of 1-s; map = Pi.map on both summands). Exact.
- c_{f,P}: `pullbackTensorPullbackTower`, levels `pullbackTensorPullbackTowerLevel` =
  reorder/restrict, Res(v^{-1}), Res f_n^*(a^{-1}) in this order. Exact.
- F^ref = L_X D_f R_Y: `pullbackTensorReferencePullback = reduction ⋙
  pullbackTensorSequenceDerived ⋙ coefficientSequenceLimit`. Exact.
- μ_{f,P}: `pullbackTensorReferencePullbackModel` = L(D_f(m_{Y,P})) ≪≫ L(mapDerivedCategoryFactors
  of F_f) ≪≫ `pullbackTensorLimitRoos` (restriction factorization then ρ_X) ≪≫ Q(H_X(c_{f,P})).
  Same four factors in the node's order. Exact.
- \hat f^*, ε: `integralDerivedPullback = (integralPullbackDescent f).functor`,
  `integralDerivedPullbackComparison = .comparison : GoodLoc ⋙ \hat f^* ≅ ι ⋙ H_X B_f^0 ⋙ Q`. Exact.
- conclusion: `∃! e : integralDerivedPullback ≅ pullbackTensorReferencePullback, ∀ P good,
  e.app (Q P) = ε.app P ≪≫ μ_P.symm`; `≪≫` is diagrammatic, so this is μ^{-1}∘ε. ∃! over
  natural isomorphisms of the full unbounded derived functor. Exact, neither weaker nor stronger.

Edge cases: n = 0 is the quotient O_E/ϖ (exponent n+1); all integer degrees; zero complexes,
empty schemes and identity morphisms are not excluded; l may be the residue characteristic;
no completeness or boundedness hypothesis. Uniqueness is the descent universal property via
`normalizedDescentComponents_existsUnique` (proof-dep lem-pur-integral-pullback-descent-components),
not detection by finite projections.

One definition per notion: F^ref, μ and `pullbackTensorLimitRoos` are defined in the item's own
module and spelled out inline in the item's statement; no other DAG node records them and no
duplicate exists in lean/Sheaf or lean/WeilConjectures (rg). All other names are owned by the
13 stmt_deps. Advisory: the module docstrings still carry the dissolved parent tag
(blueprint: def-pur-completed-pullback-tower-realizations); the existing Lean is not edited at stage 2.

No mismatch found; nothing changed except this section.
