## Worker report

The main theorem is
`WeilConjectures.IntegralSystemRealization.integralCompactificationSystemRealization`
in `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`. It concludes
`∃ o : Operations l E, Nonempty (Realizations l E D o)`. In particular existence of
the simultaneous operations is a conclusion; an arbitrary operation package is
no longer an additional hypothesis. Only this theorem has `sorry`.

The coefficient parameters are `(l : ℕ) [Fact l.Prime]`, a field `E : Type u`,
`[Algebra ℚ_[l] E]`, and `[FiniteDimensional ℚ_[l] E]`. `D : FiniteFieldDatum.{u}`
fixes the algebraic closure of the finite field and `_hl : l ≠ D.p` is exactly the
prime-to-characteristic assumption. `System` is the recorded ordinary unbounded
derived category `coefficientSequenceDerived`; it is not a diagram of derived
categories. `Integral` is the derived category over the completed coefficient
sheaf. `calculus` is the recorded, normalized `pullbackTensorCalculus`, so both
reduction and total limit, their unit and counit, and finite projections are fixed.

The clauses of the statement are rendered as follows.

- **Geometry and typing.** `Expression` is indexed by `Over (Spec (.of D.k))`.
  Thus every expression arrow is over the fixed field. Proper and quasi-compact
  open constructors retain their actual proofs. `Expression.geometric` requires
  finite type of every intermediate scheme, and separated finite type of inverse
  image and compact-support arrows. A compactification's proper ambient scheme is
  finite type over the same base; `compactOpenQuasiCompact` cancels the proper
  factor to obtain quasi-compactness of its open factor.
- **Normalized, bounded constructible systems.** `Good` requires the existing
  `IsNormalizedCoefficientSequence`, `LevelBounds`, and retained `Origins`.
  `LevelBounds` quantifies one finite cohomological interval and one finite Tor
  interval valid at every positive coefficient level, using the actual finite
  constructibility, support and Tor-amplitude predicates.
- **Origins really belong to the fibers.** `Origins.level n` is a bounded-below
  fixed-coefficient complex. `Origins.origin n` is the recorded bundled
  `FixedEtaleOriginWitness`. `Origins.evaluation n` identifies its realized
  complex with `coefficientSequenceDerivedEvaluation ... n` of the given `M`.
  `etaleTransition`, `fixedTransition`, `originSquare`, and `transitionSquare`
  retain the coefficient-restriction square on the étale antecedents and identify
  it with the actual system transition. `originRestrictionEquality` is constructed
  from `Functor.ofOpSequence_map_homOfLE_succ` applied to the specified quotient
  sequence, and `mapDerivedCategoryNatIso (eqToIso ...)` transports that equality.
  There is no freely chosen restriction comparison and no heterogeneous equality.
- **Every intermediate bound is checked.** `Expression.admissible` recurses through
  every subtree. Its compact-support branch additionally checks `Good` for
  `J_j M` on the ambient compactification, as well as the final `S_p J_j M`.
  This was missing in the returned packet. The integral input predicate is the
  recorded `sfIntegralConstructible`, including completeness and the common cohomological
  bound; `Good` separately supplies the finite Tor bounds.
- **Actual operations.** `pull` is `pullbackTensorSequenceDerived`. `Direct.model`
  is `SheafOfModules.CoefficientDerivedImage` of the actual ordinary sequence-site
  inverse/direct adjunction; its universal derived certificate and transpose
  normalization are retained. `Direct.inverse` is fixed on all cochain models by
  `factors`. `Open.ordinary` is an exact functor with its ordinary adjunction to
  this actual inverse image, and `Open.derived` and `.adj` are exact localizations.
- **Evaluation and transitions.** `DirectEvaluation` contains actual natural
  isomorphisms, unit and counit equations, the canonical quotient-restriction
  direct-image comparison, and the adjacent-transition equation. `OpenEvaluation`
  is fixed by the inverse mate of `pullbackTensorDerivedEvaluation`.
  `supportEvaluation` composes these two specified comparisons. All levels are
  indexed by `n : ℕ` representing exponent `n+1`.
- **Canonical compositors and open maps.** `Compositors.sections` fixes ordinary
  direct-image composition on sections by fiber-product pasting. `conjugate`
  fixes ordinary inverse-image composition, and `pullComp_model` fixes its
  localization on cochains. `pushComp` is its derived adjoint conjugate and
  `openComp` is fixed by open-adjoint uniqueness. `OpenComparisons` contains the
  actual open unit, cartesian beta, open tensor projection and clopen comparison,
  each with its explicit adjunction-transpose equation. The tensor comparison
  in those equations is the published K-flat normalized system comparison.
- **General proper/open squares.** `properOpenLambda` is the actual composite:
  right-adjoint conjugation of cartesian open base change, restriction through
  the fiber-product lift, inverse open unit, the canonical clopen open/direct
  comparison, and proper-image composition. It uses `StrictTower.squareLift`
  and its open/closed instances. No cartesianness of the original square is
  imposed. `ProperOpenCoherence.adjunct` fixes Gamma as the open adjunct of this
  lambda inverse. `vertical`, `horizontal` and `baseChange` are displayed
  equations of actual system maps, not proposition-valued placeholders.
- **Scalar restriction, finite evaluation, identities and refinements.** The
  coefficient-sequence category is definitionally the published varying-ring
  semilinear category at `scalarRings n = ULift A_(n+1)` and `scalarTransitions`.
  `CanonicalBridge.ordinary` is fixed to identity on every component section;
  `.pull`, `.push` and `.shriek` are derived by adjoint uniqueness/conjugation.
  `ProperOpenCoherence.canonical` is the explicit equation identifying Gamma
  under these canonical comparisons with
  `ProEtale.SemilinearProperOpen.gamma`. The published `gamma_scalarRestriction`,
  `gamma_evaluation`, `gamma_finite`, and `gamma_identities` therefore give the
  corresponding clauses for this very map. Their scalar restrictions are the
  actual termwise restrictions along the compatible quotient maps from O_E.
  Section-normalized compositors agree by uniqueness on ordinary sections.
  Refinement squares and their nested pastings are specializations of the
  displayed general horizontal/vertical equations; no faithfulness of derived
  evaluation is invoked.
- **Specified projection/exchange composites.** `properExchange` is the derived square
  mate. `properProjection` is the tensor-pullback/counit mate.
  `compactificationExchange` is that proper exchange followed by beta.
  `compactificationProjection` is proper projection, then the open projection,
  then inverse pullback composition and the actual compactification equation.
  These are definitions with real map terms in the order of
  `def-exchange-projection`, rather than fields asserting that unspecified maps
  satisfy unspecified properties.
- **Actual integral functors.** `integralInterpretation` uses the recorded
  `integralDerivedPullback`, `integralCompletedTensor`, ordinary
  `PurCompactSupport.push (completed l E)`, and localized completed-ring open
  extension. Its compact-support branch is exactly
  `PurCompactSupport.image (PurCompactSupport.completed l E) c`.
- **Canonical realization models, before evaluation.** `OrdinaryLimitModel`
  fixes the ordinary proper-image/limit comparison by every projected section.
  `ordinaryLimitProjection` transports each restriction projection with the published
  `coefficientSequenceRestriction_evaluation` equality and compares via the
  specified `pullbackTensorSequenceDirectEvaluation` map. `restrictionSection`
  is the identity function on sections for Mathlib scalar restriction;
  `integralPushSection` and `finitePushSection` are the identity coordinate functions
  for the two specified direct images. No section equivalence
  is supplied as free data.
  Its `reductionPull` is the ordinary adjoint conjugate. `RealizationModel.model`
  fixes derived reduction/pullback on whole flat-term K-flat representatives
  against `pullbackTensorReductionModel` and the localized ordinary comparison.
  `RealizationModel.push` is its right-adjoint conjugate, with the actual
  completed-ring derived adjunction. `openReduction` is its inverse
  open-adjunction mate. Thus neither comparison is a freely selected endpoint
  isomorphism.
- **Expression comparisons are fixed recursively.** `comparison` is a natural
  isomorphism of the full input-family functors on `Expression.domain`.
  `inputNormalization` fixes the variable case to the inverse actual unit.
  `pull` and `tensor` give the explicit counit-insertion recursion using the
  published K-flat pullback/tensor models. `push` uses the preceding canonical
  right-adjoint conjugate. `openNormalization` fixes open realization by the
  actual open-reduction mate and reconstruction unit; `shriek` then applies
  the inner comparison. `supportRecursion` is the same J-then-S recursion for
  the chosen compactification, with the hidden intermediate bounds retained.
- **Specified generators and all outer contexts.** `CanonicalIsoPair` lists the
  actual pullback, proper-image and open compositors, tensor reassociation,
  tensor/pullback, cartesian open beta, clopen and open projection maps with their actual
  localized integral counterparts. `BasicPair` adds their two directions, both
  units and counits, Gamma, the exchange mate, proper projection, and the recorded
  compactification exchange/projection composites. These are indexed by the
  specified maps: there is no arbitrary arrow-valued generator field.
  `Expression.completionMap` recursively composes the recorded pull-completion
  units and tensor-completion maps; it is defined independently of every c_V.
  `completionIso` asserts its invertibility on the stated domain as a conclusion.
  `CanonicalPair.basic` uses its inverse at the source and itself at the target
  to transport the specified localized integral map. `CanonicalPair` then closes
  under identity, composition (retaining admissibility and geometry of the
  intervening expression), and the six actual expression constructors, with
  both tensor slots. `supportExpansion` identifies a compact-support symbol with
  its actual J-then-S expression over the base, so nested compactification
  composition maps are generated by Gamma and the proper/open compositors.
  `coherence` states `L(s) ≫ c_T = c_V ≫ r` for those pairs.
  The old arbitrary-arrow counterexample cannot instantiate any constructor.
- **Tensor/square compatibility.** `ringedTensorCoherence` states the displayed
  projection-first equals exchange-first equation from the recorded
  `lem-weil-pbc-ringed-exchange-tensor-coherence`, using the very exchange mate,
  tensor/pullback comparison and square compositor defined in this packet.
- **The compact-support endpoint is projection-normalized.** `compactSupport`
  is an explicit equality with the actual
  `PurCompactSupport.comparison (reduction ...) c`, `finiteReductionIso`, and
  `finiteImageIso`. Its other side is the actual reduction/limit counit,
  `supportEvaluation` and the inner comparison. Together with `supportRecursion`
  this fixes the recorded compact-support functor and its finite projections.

Dependency declarations used directly include `FiniteFieldDatum`
(`Sheaf.Paper.FiniteFieldFiber`); `Padic.coefficientExtensionRing` and its transitions
(`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`); the
`CoefficientDerivedSystemCalculus` interfaces (`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`);
`sfIntegralConstructible` (`Sheaf.Paper.SfIntegralConstructible`);
`HasProEtaleTorAmplitude` (`Sheaf.Paper.FiniteTorAmplitude`);
`FixedEtaleOriginWitness` (`Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`);
`CoefficientDerivedImage` (`Sheaf.Paper.CoefficientSystemDerivedComparison`);
`OpenTensorNormalization.exactDerivedAdjunction`
(`Sheaf.SixFunctors.OpenTensorNormalization`); `StrictTower.squareLift` and the
strict-tower calculus (`Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`);
`ProEtale.SemilinearProperOpen` operations and normalized maps
(`Sheaf.SixFunctors.SemilinearProperOpenMatePasting`);
`pullbackTensorCalculus`, `pullbackTensorReductionModel`,
`pullbackTensorIntegralPullbackModel` and `pullbackTensorIntegralTensorModel`
(`Sheaf.Paper.CompletedPullbackTensorComparison`); `PurCompactSupport` coefficient,
adjunction and image constructions (`Sheaf.Paper.IntegralCompactSupportCoefficientData`);
its `finiteReductionIso`, `finiteImageIso` and `comparison`
(`Sheaf.Paper.IntegralCompactSupportCoefficientComparison`); the recorded qcqs
support realization (`Sheaf.Paper.QcqsCompactSupportRealization`);
`sfRealizationRestriction` and `sfDerivedImageRestriction`
(`Sheaf.Paper.SfCompactSupportRestrictionOfScalars`); and
`ProEtale.pbcDerivedComparisonRestrict` (`Sheaf.Paper.WitnessCompatibility`).
The repaired bridge also uses `OpenFactorCoherence.Pull`, its `.unit`,
`OpenFactorCoherence.Tensor` and its `.chi` from
`Sheaf.SixFunctors.OpenFactorPullModel` and `OpenFactorTensorModel`.
`SuppliedExchangeProjection.compactificationExchangeFromData` is from
`Sheaf.Paper.ExchangeProjectionSuppliedDomains`; the tensor-square equation is
from `Sheaf.Paper.RingedExchangeTensorCoherence`.
Mathlib supplies `Over`, pullbacks, `Adjunction`, conjugate and mate equivalences,
exact derived localization, functor products and Pi input families. Published
proof dependencies are imported as ordinary imports in the theorem module.

The main docstring now contains all seven DAG proof steps, including the actual
expression-tree recursion, the counit formula for reduction, and the separate
outer-context induction. Every helper has its owning node's source/blueprint
docstring. Node `lean.declarations` lists every delivered named declaration, and
`lean.statement` is extracted verbatim from the main signature.

Edge cases checked: the empty finite input family (no expression can use an absent
variable); zero and rank-zero inputs; tensor with zero; the empty open; identity
open, identity proper arrow and identity square; general noncartesian proper/open
squares; a single compactification; nested compactifications and a proper
refinement; adjacent and composite quotient transitions; and all positive levels
including exponent one. No equality of morphisms is inferred from finite derived
evaluations. No statement change or STATEMENT-DISPUTED flag is needed.

Searches: the retained packet's LeanFinder query for derived adjunction/evaluation
returned eight ordinary module-adjunction hits, none this statement; Loogle
`"Adjunction", "mate"` returned zero; Mathlib grep for normalized systems,
semilinear systems and derived completion returned zero. The repair additionally
ran LeanSearch for coherent realization of finite derived expressions by derived
inverse limit (eight hits concerning ordinary direct limits/adic completion,
none matching), LeanFinder for coherent integral realization of proper image/open
extension/pullback/tensor (eight unrelated topological/condensed hits), Loogle for
adjunction mates (zero), and Mathlib CategoryTheory grep for the realization and
proper/open names (zero). `rg` over upstream `WeilConjectures` and project
`lean/Sheaf` found no existing expression-domain/bridge declarations.
`blueprint_refs.py search` found no node for this interface. The general published
semilinear proper/open calculus is reused through its section-normalized bridge.

## New nodes

`def-sf-integral-system-operations` defines the single simultaneous canonical
operation package and its explicit mate/compositor helpers. Its source is the
strict-system portion of the item's blueprint proof and Stacks 0941/03DI/07A7.
The searches above found no existing interface joining these exact recorded
coefficient-sequence operations with the needed normalizations.

`def-sf-integral-system-expression-domain` defines finite typed expressions and
their actual bounded/origin domain, including the hidden open-extension object
in compact support. Its source is the expression-induction and common-bounds
proviso in the item's blueprint proof. Existing operation syntax for completed
pullback/tensor lacks proper image, open extension and compact support, so it
cannot replace this syntax/domain.

`def-sf-integral-system-canonical-bridge` defines the section-normalized bridge to
the existing semilinear proper/open calculus and the ordinary/derived integral
realization model. Its source is the same blueprint's coefficient-comparison
route and Stacks 03D7/07A4/07A6/0941. It uses the published semilinear calculus and
published K-flat reduction models; no existing node joins their actual functors
with these section- and adjunction-normalized comparisons. All three new nodes
record the three kinds of search, exact ancestry, and their own modules.


## Returned points repaired

This repair addresses immutable head `25edfecdc076` and all five numbered points.
R1: only the specified canonical system/integral generator pairs enter coherence.
R2: the unused arbitrary `canonicalGenerators` and `whiskering` fields are removed;
whiskering is an inductive closure with actual operation-map indices used by the
coherence equation. R3: `properExchange` is again the explicit `mateEquiv` of the
specified square compositor, including in base-change pasting. R4: proper
projection and both compactification composites are restored from their recorded
adjunction/tensor formulas; their pairs and the tensor-square equation are present.
R5: transitions use equality transport of the actual quotient restriction, and
ordinary limit comparison is fixed by equality of the projected sections after
the published restriction-evaluation equality transport and canonical direct-image
evaluation map.
No free restriction iso or projection equivalence remains.

## Second reading by Q22

This is a sequential self-review; the dispatcher forbids sub-agents. The identity
and nonzero edge case from R1 was checked: an identity system arrow paired with a
zero integral arrow cannot be generated by `CanonicalIsoPair` or `BasicPair`.
The localized integral maps are fixed before the realization family is introduced,
so coherence does not define them by conjugation through c_V. The completion maps
are actual normalized maps from the published models. The generator closure uses
all six expression constructors, including both tensor slots and compact support.
The source's input and intermediate bounds, geometry, coefficient sizes, seven
proof steps, and compact-support finite-projection pinning are retained.
No change to the item's mathematical statement was made.

Additional repair searches: LeanFinder for canonical paired structural maps between
finite derived expressions with completed integral realization and arbitrary
whiskering returned eight unrelated `MoveAdd.pairUp` and monoidal/bicategory tactic
expression-parser declarations. Loogle for `mateEquiv` and
`rightAdjointProjectionMap` returned zero. `rg` for `CanonicalIsoPair`,
`CanonicalPair`, `RingedModels` and `Expression.completionMap` in the shared and
upstream Lean trees returned zero. Blueprint node search for paired structural
maps returned zero. The existing published pull/tensor completion models and
exchange/projection interfaces were reused.

## Validation

The initial saved-packet dry run was run as requested and rejected its malformed
projection signature. The repair corrected that signature. Subsequent file-only
compilation diagnosed missing explicit quotient-restriction exactness instances
and a parenthesis in the section projection equation; these were repaired.
Server confirmation compiled all four revised files successfully (operations
14.0 s, expression domain 6.8 s, canonical bridge 20.2 s, main 30.7 s). The main
file had one empty-line style warning, which was removed before the final check.
The wrapper also recovered from a missing live dependency artifact by its
authorized server confirmation.

Final `scompile.py` of all four delivered files exited 0 with no warnings. Their
library-name checks took 13.6 s, 6.3 s, 20.0 s and 29.4 s, respectively, within
the required 60-second per-file limit. Every delivered variable/universe is
explicit, all definition data is real, and the sole `sorry` is the item theorem.
The main projection mates use Mathlib `Functor.curryObjProdComp` to normalize
the comparison into the exact curried shape of `rightAdjointProjectionMap`.
Over-category composite and compactification geometry instances are supplied
with their actual underlying scheme arrows explicitly typed.

The final delivery dry run compiled all four files cleanly. Its preflight found
two combined dependency citations in the new bridge node; each has been split
into the required individual bracketed citation, without changing the statement.
