## Worker report

Item: lem-pur-completed-unit-pullback-tower. Group N7, stage 2.

The module `Sheaf.Paper.CompletedUnitPullbackTower` states
`WeilConjectures.CompletedUnitPullback.completedUnitPullbackTower`. Its conclusion
is `Nonempty (Result P f)`, a package containing the specified integral unit
isomorphism, its finite and whole-system formulas, and precisely its rational and
common-stage images. The only postponed proof is this theorem. All helper data
are actual constructions from the recorded APIs; none is a new chosen map.
The theorem's docstring gives the complete six-step natural-language proof.

### Hypotheses and objects

* `P : PurityFiniteSetting` supplies the algebraic closure of a finite field,
  its characteristic, the distinct coefficient prime, the fixed algebraic closure
  of Q_l, and the literal finite intermediate field `P.extension`. The valuation
  ring, uniformizer and quotients are the existing Padic coefficient constructions.
  The setting also contains an auxiliary positive level; the conclusion uses all
  levels and is independent of that auxiliary choice.
* `X Y : Scheme`, their `Over (Spec (.of P.field.k))` instances, and the six
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` instances render
  separated finite-type k-schemes. These properties apply to the structural
  morphisms, not to f. `f : X ⟶ Y` with `f.IsOver` is any k-morphism. No smoothness,
  properness, finite Tor dimension, or nonemptiness hypothesis on f was added.
* The sites are the existing `Scheme.ProEt.topology W`. The library numbers
  positive quotient exponents by `n : ℕ` representing exponent `n+1`.
  `integralCoefficientSheaf l E W n` is B_(W,n+1), and
  `integralConstantCoefficientObject l E W` is the completed regular coefficient
  sheaf in degree zero, not the discrete constant valuation-ring sheaf.

### Every conclusion clause

* `Core.admissibleX` and `.admissibleY`, through `Admissible`, assert
  `finiteTorConstructibleIntegral l E W U`. The first conjunct of this property
  is the recorded integral constructibility condition, including derived
  completeness. Every `constantCoefficientReductionMap l E W n` is an isomorphism.
  This is the actual reduction multiplication from the existing completed sheaf,
  not an existentially chosen equivalence with the finite coefficient object.
* The same `Admissible` field gives, for every n, cohomological support contained
  in `Set.Icc 0 0` and `Scheme.HasProEtaleTorAmplitude ... 0 0`, with a common
  interval independent of n. `IsLocallyConstantProEtaleModuleSheaf` for the actual
  finite regular module on W expresses the single constructible stratum W.
  Finiteness of that rank-one module is built into the existing finite coefficient
  construction and the integral constructibility predicate.
* `systemUnit` is the regular module on the existing coefficient sequence ringed
  site, and `systemObject` is its degree-zero derived object. Thus every quotient
  transition is already in the object. It is not a product of unrelated derived
  evaluations. `Reduction.finite` identifies its ordinary evaluations with the
  regular finite coefficient modules, and `finite_sections` requires the identity
  on every underlying section, using HEq solely for the differently presented
  coefficient types.
* `Reduction.comparison` identifies the actual derived reduction system of U with
  this whole strict quotient system. `Reduction.reduction` identifies each finite
  component with the existing canonical reduction map under the recorded
  `reductionEvaluation` and exact single-complex evaluation comparisons.
  `Reduction.augmentation` identifies U with the specified total limit, and
  `augmentation_eq` fixes its arrow to the actual adjunction unit followed by the
  limit of that whole-system comparison. This is the augmentation identity needed
  in the node's corrected stage-1 proof; it is explicitly part of the statement.
* `Core.normalizedX`, `.normalizedY`, and `.normalizedPull` use the existing
  `IsNormalizedCoefficientSequence`, defined by the quotient-restriction Hom
  bijectivity criterion of `NormalizedDVRTower`. These are whole normalized
  derived systems with the library's actual semilinear transitions.
* `finiteMultiplication` is the adjoint of Mathlib's
  `SheafOfModules.unitToPushforwardObjUnit` for the actual pro-etale coefficient
  ring map. It is the finite unit multiplication, with no map parameter.
  `Core.finite_iso` asserts its invertibility for every positive exponent.
* `systemMultiplication` is the identical construction on the coefficient sequence
  ringed site, using `PrimitiveCounit.ringMap` and its specified adjunction.
  `systemMap` is its derived arrow under the exact single-complex comparison.
  `Core.system_iso` asserts it is an isomorphism. `Core.finite_components` identifies
  its ordinary components with the very finite multiplications, via the canonical
  `PrimitiveCounit.inverseEvaluation`. Hence all actual quotient transitions
  commute before localization, not just as an unspecified family of isomorphisms.
* `Core.realization` compares the specified `integralDerivedPullback` with derived
  reduction, whole-system pullback, and the specified coefficient-sequence limit.
  `Core.realization_model` is the existing `PrimitiveCounit.PullModel` predicate:
  it fixes this comparison on K-flat strict reduction systems and the normalized
  Roos comparison. `Core.roos` supplies that existing normalized realization.
  An arbitrary natural isomorphism would not satisfy this representative condition.
* `Core.unit` is the asserted completed pullback isomorphism. `unit_formula` fixes
  its arrow to the specified realization followed by total limit of the actual
  system multiplication and inverse of the actual augmentation on X.
  `coherent_reduction` is an equality in the whole derived system category:
  reduction of this same arrow, followed by the target comparison, is the actual
  reduction/limit counit followed by pulled source comparison and `systemMap`.
  It includes the source realization and its reduction, with every domain explicit.
  This is the strong system-level equality, not an assertion inferred from
  pointwise isomorphisms at every level.
* `integralObject` is exactly U in the full constructible subcategory, with only
  its membership proof supplied. `rationalObject` is its image under the recorded
  raw rational localization. `rationalSource` uses the existing specified
  unchanged-object identification of rational pullback. `rationalMap` is exactly
  the image of the integral arrow under that localization, with that source
  identification. `Result.core` uses the literal field `P.extension`, and
  `Result.rational` asserts this very rational unit arrow is an isomorphism.
* The recorded common-stage category uses the small model of its finite subfield.
  `coefficientStage` is exactly the chosen intermediate field E, and
  `coefficientModel` is the existing `AlgebraicallyClosedCoefficients.Coefficient`
  for that stage. `modelEmbedding` is the canonical Shrink algebra equivalence;
  `modelScalar` is its existing scalar-extension functor. `modelUnit` is the
  existing normalized scalar-unit isomorphism, not a new choice of unit arrow.
  `Result.model` supplies the same integral calculation over this algebra-equivalent
  model, and `model_rational` its rational image. Crucially `Result.model_square`
  relates this map to the literal E map by the existing pullback-scalar comparison
  and the specified scalar-unit comparisons. Thus the size convention does not
  silently discard the literal E integral and rational statements.
* `commonObject` is the actual common-stage inclusion of that rational unit at the
  chosen E-stage. `commonSource` is the recorded common-stage pullback's specified
  unchanged-stage comparison. `commonMap` is the actual inclusion of the rational
  arrow, and `Result.common` says it is an isomorphism. The preceding square makes
  it the image of the literal E integral arrow under canonical size transport.
  The explicit completed integral object and its membership proof are the lattice
  presenting both field units; no extra arbitrary lattice is introduced.

### Dependency declarations used

All original statement dependencies were inspected, including their complete
recorded signatures and docstrings. The scheme-morphism convention node has a
convention-only Lean record, so the actual Mathlib morphism properties are used.

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `PurityFiniteSetting.coefficientPrime_isUnit_stalk`. The local
  `residueInvertible` instance transports this unit through the actual residue
  homomorphism; it adds no invertibility hypothesis to the theorem.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, its topology,
  `Scheme.proEtaleBaseChange`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and the imported coefficient
  construction modules: `completedIntegralCoefficientSheafUnrestricted`,
  `integralConstantCoefficientObject`, `integralCoefficientSheaf`.
* `Sheaf.Paper.IntegralReductionTowerCanonical`: the canonical reduction tower
  and its actual quotient transitions, used through the normalized reduction API.
* `Sheaf.Paper.NormalizedDVRTower` and `Sheaf.Paper.CoefficientRingedSequenceSite`:
  `NormalizedDVRTower`, `coefficientSequenceCommRingSheaf`,
  `coefficientSequenceModules`, `coefficientSequenceDerived`,
  `coefficientSequenceEvaluation`, `coefficientSequenceDerivedEvaluation`,
  `coefficientSequenceLimit`, `IsNormalizedCoefficientSequence`.
* `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `coefficientDerivedSystemEvaluationCalculus`,
  including its actual reduction/limit adjunction and normalized finite reductions.
* `Sheaf.Paper.CompletedPrimitiveCounitComparison`: `PrimitiveCounit.base`,
  `ringMap`, `direct`, `inverse`, `pull`, `inverseEvaluation`, `RoosRealization`,
  and `PullModel`. These supply the canonical whole-system geometric interface.
* `Sheaf.Paper.QuotientCornerFrobeniusStructures`: the existing specialized
  sequence-site sheafification and locally-bijective instances. Importing these
  reuses the existing size-compatible instances, instead of defining duplicates.
* `Sheaf.Paper.ConstantCoefficientScalarNormalization` and its public imports:
  `constantCoefficientReductionMap`, `constantCoefficientRationalScalarIso`,
  `constantWeilIntegralObject`, `constantWeilRationalObject`. The last two are
  definitionally the same completed unit objects used here (membership proofs
  are proof irrelevant).
* `Sheaf.Paper.FiniteTorAmplitudeSites` and its public imports:
  `finiteTorConstructibleIntegral`, `proEtaleCohomologicalSupport`,
  `Scheme.HasProEtaleTorAmplitude`, `IsLocallyConstantProEtaleModuleSheaf`.
* `Sheaf.Paper.DerivedPullbackTensorHom` and its public imports:
  `integralDerivedPullback`, `constructibleIntegralPullback`,
  `rationalDerivedPullback`, `rationalDerivedPullback_existsUnique`,
  `rationalPullbackScalarComparison`, `commonStageDerivedPullback`, and
  `commonStageDerivedPullback_existsUnique`.
* `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfIntegralConstructibleCategory`, `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalScalarExtension`.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`,
  `GeneralAlgebraicallyClosedCoefficients.inclusion`,
  `AlgebraicallyClosedCoefficients.Index`, `Coefficient`.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree`:
  `SheafOfModules.unit`, `unitToPushforwardObjUnit`; the actual coefficient module
  adjunction and exact `mapDerivedCategorySingleFunctor` comparisons are reused.

The item's `stmt_deps` gains four already-landed interface nodes:
`def-coef-ringed-sequence-site`, `lem-coef-derived-system-evaluation-calculus`,
`lem-pur-completed-primitive-counit-comparison`, and
`lem-weil-constant-coefficient-objects-constructible`. Their dependency closures
were checked not to contain this item. No new mathematical node or dependency
repair is needed. The original statement, proof, and all other fields are unchanged.

### Edge cases and source check

The local blueprint proof first sentence applies purity to the coefficient;
the node's six detailed steps specify the coherent completed-unit prerequisite.
They agree with the formulas above. Empty X or Y gives zero module categories;
local constancy and both support bounds remain valid, with the empty stratum
permitted. For the identity f the actual ring-map adjoints give multiplication
and hence the identity under the canonical comparisons; there is no assumption
excluding this case. Exponent one is n=0 in the existing API. Ramified E is
allowed: every quotient is by its own existing uniformizer, not by l. The
parameter n never selects a single level for the theorem. A general k-morphism
need not be smooth or have finite Tor dimension: pullback of the regular
coefficient unit remains the unit. Cohomological and Tor supports may be empty,
so bounds are expressed as containment, not nonzero cohomology at degree zero.
All variables and the universe u are explicitly bound, with autoImplicit false.

### Searches for an existing statement

The following prescribed searches were run (also recorded by msearch.py):

* LeanFinder: "The completed coefficient unit is derived complete with uniform
  Tor amplitude zero and its coherent quotient system is preserved by derived
  pullback". Eight hits concerned BDeRham/BDeRhamPlus, adic completion, formal
  smoothness, and IsAdicComplete; none states the sheaf or coherent-system result.
* Loogle: "SheafOfModules.pullback, SheafOfModules.unit". Six hits included
  `SheafOfModules.pullbackObjUnitToUnit`, its final-functor isomorphism instance,
  and the ordinary adjunction identities in PullbackFree. Their full declarations
  were read. They provide the finite ordinary-unit construction only, not this
  completed-system theorem.
* Mathlib grep through msearch.py:
  `completedUnitPullback|pullbackObjUnitToUnit|IsNormalizedCoefficientSequence`
  under Algebra/Category/ModuleCat/Sheaf. Only five PullbackFree hits; no exact
  completed-unit or normalized-system theorem.
* Direct rg of the item id in lean/WeilConjectures returned no declaration.
  Direct rg for `completedUnitPullback|CompletedUnitPullback` in lean/Sheaf
  returned no previous module. Broader completed-unit/reduction searches located
  the reused constant-coefficient and coefficient-system modules, which were read.

No statement is disputed. The pre-existing Q37 `reviewed` record concerns its
stage-1 proof split, not a stage-2 statement: the live node had no `lean` or
`reviewed_lean` field when this work began. Therefore this is an ordinary stage-2
statement delivery, not a second split or a repair of a reviewed Lean statement.

### Validation

The final module passed scompile.py in module mode, both the sandbox check
(18.2 seconds) and its real library module name (19.5 seconds), with no errors
or disallowed warnings. Automatic structure size-specification and injectivity
lemmas are disabled locally for the three data packages; they are not used in
the statement, and avoiding their generation keeps compilation below 60 seconds.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
