## Worker report

The module `Sheaf.Paper.QuotientExpressionStrictKFlatTowers` states
`WeilConjectures.StrictQuotient.quotientExpressionStrictKFlatTowers`, with its proof
left `sorry`. All helper definitions have explicit data. The node's statement,
statement dependencies and proof are unchanged.

Sources read: Stacks `sites-cohomology.tex`, Tag 07A2,
`lemma-tensor-product-K-flat` (lines 3060 onward), and Tag 0G7E,
`lemma-pullback-K-flat` (lines 3508 onward); the item's ten-step extracted proof
and `def-pur-strict-quotient-expressions`. These sources require unbounded
K-flat complexes, flat terms for pullback, and no flatness of a coefficient map.

Hypotheses and clauses, in statement order:

* `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
  and `[FiniteDimensional ℚ_[l] E]` give exactly the prime and finite extension.
  The recorded coefficient extension supplies its chosen uniformizer and quotient
  rings. No extra norm or topology on E is hypothesized.
* `{Z X Y : Scheme.{t}}`, `h : Z ⟶ X`, `f : X ⟶ Y` and the three residue-field
  `IsUnit (l : W.residueField x)` hypotheses express the schemes, morphisms, and
  invertibility of l. Universes t and u remain independent; the module universe
  is `max u (t+1)`. The original small sites retain object size t+1 and arrow size t.
* `r : ℕ` and `P : Fin r → CochainComplex (scalarReductionSource l E Y) ℤ`
  give the finite possibly empty list of completed-coefficient complexes.
  `hP` is the recorded `IsKFlatIndependentCoefficients`; `_hflat` is
  `IsFlatOnSite` in every integer degree. The completed coefficient sheaf is the
  actual inverse limit, rather than the discrete constant ring of integers.
* Natural-number level n means the positive exponent n+1, as in all the recorded
  coefficient modules. `coefficientFiniteQuotient` and the completed projections
  are the actual quotient and limit maps.
* `Expression h f r W` is the constructor-history refinement of the recorded
  `Generated` predicate: inputs at Y, the degree-zero units at Y/X/Z, total tensor
  at a common scheme, and pullback along f, h, h followed by f. No quotient of the
  syntax is taken. `Expression.interpret` uses the recorded `Complex`, `total`
  and `pull` without defining any second tensor, pullback, or module category.
* `coefficientInverseImage` is the specified Kan-extension/sheafification inverse
  image transported to the compatible small model. `coefficientToModel` is the
  actual AsSmall transport. `constantCoefficientMap` is explicitly the adjunct of
  the recorded constant-section direct-image ring map, not an arbitrary map.
  The first conjunct asserts its invertibility, finite-limit and finite-colimit
  preservation for `integralOperationsLevelPullback`, and exactly the coefficient
  square for every `AllowedArrow h f g` and every n ≤ m.
* `unitSection` identifies the degree-zero unit term with its coefficient module.
  The second conjunct states that its actual horizontal map sends b to q(b).
  The zero terms in other degrees and restriction/differential compatibility are
  already part of this actual single complex.
* The existential `N` and chain isomorphisms `κ i n` identify all input levels
  simultaneously with the prescribed ordinary scalar reductions of P i.
  Their first equation identifies the actual horizontal chain map, under κ,
  with `coefficientOrdinaryQuotient`: x tensor b goes to x tensor q(b).
  The next equation pins the derived input comparison to
  `coefficientFiniteReductionModel` followed by `Q.map (κ i n).inv`.
* For every expression, `SystemGood` requires K-flatness and flat terms over the
  sequence ring itself. `Good` requires the same two recorded notions at each
  finite coefficient level. This asserts no flatness after restriction to the
  completed coefficient ring.
* The next two equations state `horizontal` identity and composition on every
  section in every degree, with every pair n ≤ m ≤ a, including equality.
  Because these are the actual maps of the module presheaf, scalar restriction
  composition is the identity on section groups. Each `transition` is a morphism
  of cochain complexes, so restriction compatibility, semilinearity, the chain
  equation, and square-zero differentials are intrinsic to its type. The total
  complex is the recorded direct-sum total with its sign (-1)^p.
* `TensorTransitions` explicitly asserts the formula on each pure tensor in every
  total-degree summand. `PullbackTransitions` asserts the formula on the actual
  adjunction-unit generators. The horizontal maps are module-presheaf maps over
  q, so on scalar multiples this is precisely q(s) times that generator formula.
  These predicates were read in the dependency module and reused unchanged.
* The exact-localization comparison for `coefficientSequenceDerivedEvaluation`
  computes evaluation on the interpreted complex itself. The system tensor
  comparison is pinned to `CoefficientTensorModels.iso` on these same K-flat
  inputs, for every normalized coefficient tensor calculus S. The finite tensor
  comparison is pinned to `tensorComparison`, which first localizes the ordinary
  evaluation/total-tensor comparison and then applies the finite K-flat model.
  No intermediate expression is replaced by another resolution.
* For every permitted g and expression, `PullbackModel` pins the level comparison
  on actual inverse-image unit generators. `PullbackComputes` says that every
  universal left-derived pair is computed on that level complex. At the system
  level the displayed isomorphism is pinned to the exact-localization factor of
  `integralComparisonSequencePullback` on the same complex. Evaluation of that
  representative is exactly the preceding generator-pinned level model.
* `completedTower` is the actual `coefficientSequenceRestriction`, applied
  termwise, producing a complex in `ℕᵒᵖ ⥤ scalarReductionSource l E W`.
  Its localization is explicitly computed before evaluation. `completedTowerLevelIso`
  composes the exact-localization factors with `coefficientRestrictedEvaluationIso`,
  giving precisely `Res_n QK_n`. The HEq clause identifies every ordinary tower
  arrow with the actual horizontal section map. The last transition equation
  identifies its derived transition, constructed by `Localization.liftNatTrans`,
  with localization of that actual ordinary arrow. This supplies the coherent
  derived tower part of `NormalizedDVRTower`, without asserting normalization.
* There are no bounds, constructibility, inverse-limit preservation, or quotient
  flatness hypotheses. `S` only quantifies over presentations of the recorded
  derived tensor universal models, rather than adding an existence assumption.

Dependency declarations used:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and reexported coefficient rings,
  chosen uniformizer and transitions.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleSheafInverseImage`, its adjunction and constant-section maps;
  the coefficient-size versions `coefficientProEtaleModelBaseChange` and
  `coefficientProEtaleDirectRingMap` preserve the same small site and construction.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and its reexported unrestricted
  completion and actual projections.
* `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
* Mathlib `Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and its actual sheafified tensor;
  Mathlib `Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
* `Sheaf.Paper.StrictQuotientExpressions`: `Complex`, `level`, `transition`,
  `total`, `pull`, `Good`, `horizontal`, `TensorTransitions`, `PullbackTransitions`,
  `AllowedArrow`, `PullbackModel`, `PullbackComputes`, `tensorComparison`.
* `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` reexports
  `SheafOfModules.DerivedChangeOfRingsCochainModel`; the coefficient calculus
  specializes its universal counit as `coefficientFiniteReductionModel`.
* `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
* `Sheaf.Paper.SemilinearSystemModels`: `SemilinearSections.Systems` and exact
  evaluation on the vertical sequence site; the concrete coefficient specialization
  is `coefficientSequenceModules` with its derived evaluation and restriction.
* `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`,
  `normalizedDVRModuleRes`, identity-on-sections restriction composition, and the
  coherent derived-tower convention. Only that coherent part is asserted here.

The module also imports every recorded proof-dependency module for stage 3:
constant comparison/exactness/ring maps, K-flat pullback and total tensor,
strict-system/sequence-site equivalence, semilinear derived sections, and exact
functor localization. Some definition modules enter through the public constructor
module, which reexports their recorded declarations.

Edge cases checked: r=0 leaves the three units and all constructors available;
zero inputs; empty schemes; m=n and n=m=a; arbitrary integer cochain degrees and
unbounded direct-sum totals; independent scheme/coefficient universes; nonflat
quotients such as Z/l² → Z/l. No Nonempty generator assumption, field
characteristic choice, or equality of scheme and coefficient universes is added.

Searches (recorded in the pre-interruption `searches.jsonl`):

* msearch grep, `KFlat|semilinear.*tower|sequence.*site`, subdirectory
  `Algebra/Homology`: successful, zero hits.
* msearch loogle,
  `CochainComplex.IsKFlatIndependentCoefficients, SheafOfModules.IsFlatOnSite`:
  zero hits, with diagnostic unknown identifier for the project-specific predicate;
  this is not evidence that the project predicate is absent.
* msearch leanfinder, `Finite tensor and inverse image expressions of K-flat
  quotient sheaf complexes form strict semilinear towers with flat terms and
  K-flatness on the sequence site`: eight ordinary Module.Flat exactness hits,
  including `Module.Flat.lTensor_exact`, none the prescribed tower statement.
* Project rg for `quotientExpression|strictKFlatTowers|StrictQuotient.Expression|SystemGood`
  found only the separate normalization theorem in
  `Sheaf/Paper/QuotientExpressionKFlatNormalization.lean`; rg for the item id in
  WeilConjectures returned no match. The existing normalization theorem does not
  supply the present constructor-history and system-flatness statement.

Validation: the prescribed `scompile.py` compiled both the isolated sandbox module
and its actual library module name cleanly (55.3 s and 59.0 s); no error or warning.
No library or global build was run, and no live source was edited.

## Second reading by Q120

Author's direct-dispatch self-check; independent mathematical review is the
maintainer's responsibility under the dispatched brief. I reread the node and
`StrictQuotientExpressions.lean` against the delivered signature. The tree is
retained in Type rather than identifying all witnesses of the Generated Prop.
Every input κ identifies ordinary complexes and their actual quotient arrows;
unit, tensor and pullback formulas refer to the ordinary recorded constructors.
`Good` is checked at each level, and `SystemGood` uses the sequence ring, not R_W.
The localization clauses use the derived category of actual completed towers,
not a functor of independently chosen derived objects. Both the ordinary HEq
and derived-transition square specify its arrows. All three allowed arrows and
all equality-index cases are retained. No node statement correction, new DAG
node, or dependency-record repair was needed. The additional helpers are local
to this node's canonical syntax and comparison interfaces and are all listed in
`lean.declarations`; they do not replace existing coefficient or tensor notions.
