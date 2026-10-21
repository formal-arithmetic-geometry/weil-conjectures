## Worker report

Item `lem-sf-package-compactified-tower-comparisons`, group Q12, stage 2.
Module `Sheaf.Paper.CompactifiedTowerComparisons`; main declaration
`WeilConjectures.sfPackageCompactifiedTowerComparisons`. The declarations in the
node's `lean.declarations` jointly state the node. Every theorem is `by sorry`;
helper definitions construct the actual arrows or package explicit equations.
The node changes only in `lean`. There are no new nodes, dependency repairs,
statement corrections, or disputed statements.

Source: current blueprint `main-20261015`,
`sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md`, the sentences
“For (2)”, finite ordinary quotient comparison, normalized tower reconstruction,
and composition/proper coincidence in clause (3), together with this node's
18-step proof. The natural-language proof is distributed among the theorem
source/proof docstrings. The source-based statement itself is unchanged.

### Repair of the immutable-head return

The initial prescribed dry run of the saved packet passed mechanically at
`dc037831ec2`. The required statement self-check still reproduced the independent
reviewer's two findings, so this delivery changes the mathematical statements and
constructions; it is not an unchanged rebase or re-push of `8f9baa7fd194` or
`84d348dc`. The current read clone has no landed module for this item. Its node
and this packet agree outside `lean`. The live source of
`Sheaf.Paper.SixFunctorOperationDatumStages` was also read with `scompile.py --source`,
including `supportProjection` and `directProjection`.

1. **H3/H5, coefficient laws and refinement coherence.**
   Removed the two generic comparison-refl/transitivity conjuncts, which merely
   repeated `SixFunctorPushStage` fields. `SfPackageCompactSupportCoherence`
   now packages the unit and associativity conclusions, which the return said
   to retain. Replaced the old `SfPackageSupportCoefficientLaws` on a
   `SixFunctorCoefficientComparison` with literal model formulas: a target
   comparison, compositor, or proper identity component is the image of the
   source component under rational localization or common-stage inclusion.
   It has no coefficient-comparison record argument. `HEq` transports exactly
   the recorded model object equalities.

   `sfPackageIntegralSupportReduction` is the scalar extension of the retained
   support-value equality followed by `sfCompactSupportChosenReduction`.
   `sfPackageIntegralWitnessReduction` then uses the actual input witness and
   `sfIntrinsicCompactSupportComparison`; the composite helper uses both
   actual projection adjuncts. `sfPackageCompactifiedTowerNormalizedReduction`
   equates the reduced integral refinement with
   `refinementComparisonIsomorphism`, and the reduced inverse integral
   compositor with `sixFunctorFiniteCompositionComparison` at the very same
   witness. Thus the assertion concerns the recorded finite maps and the
   actual reductions, rather than only laws supplied by a comparison record.
   The extra argument is the datum's existing
   `SixFunctorIntegralNormalization`, not a new geometric or Tor hypothesis:
   instantiate with `S.higher`, `S.integralNormalization`, or with
   `S.closure.coefficientStages E₀`, `S.coefficientIntegralNormalization E₀`.

   `sfPackageCompactifiedTowerStageCoherence` states the literal localization
   formulas for the main coefficient field and every small coefficient field,
   and the literal inclusion formulas for every common-stage presentation.
   `sfPackageCompactifiedTowerFieldPassage` additionally quantifies over every
   `h : E₀ ≤ L`, including reflexive extensions. Its support, composite and
   direct transports are constructed from the actual common-stage inclusion
   comparisons and `stageSystem.transIso`. Its three equations compare the
   included enlarged-stage refinement, composition and proper identification
   with the same common-stage maps. They do not restate the
   `coefficientTransition.compactification/composition/properIdentity` fields.

2. **H3, canonical proper limit.**
   Replaced the independent `∃ e : M ≅ L.obj` conclusion in
   `sfPackageCompactifiedTowerProperTransitions` with projection equations for
   the constructed `sfPackageIntegralProperLimitIso`. That definition is
   literally the inclusion's image of
   `(S.higher.integral.properIdentity f).app K`, followed by the equality with
   `S.higher.integralDirectLimit f K`. The support-side projection is the
   chosen Roos projection transported through the datum's actual support-value
   equality (`sfPackageIntegralSupportProjection`). Thus the theorem pins the
   datum's proper identity to both strict quotient transitions and the retained
   projections of the specified limits. No unspecified triangle completion
   supplies the isomorphism. Removed the unused
   `sfPackageStrictProperComparison` helper, which had not occurred in a
   statement. The proper/open strict calculus remains a proof import.

The finite witnessed refinement theorem, the ordinary/support reduction theorems,
effectivity and uniform constructibility, units and associativity, and finite and
higher proper-exchange equations are retained. Docstrings and the declaration
record have been updated to describe the actual repaired suite.

### Hypotheses and objects

| Node hypothesis or object | Lean rendering |
| --- | --- |
| Algebraically closed finite-field base of characteristic p | `D : FiniteFieldDatum.{u}`, its `D.k` |
| Prime l different from p | `C : D.CoefficientDatum`, `C.l`, its prime instance and `C.different`; `sfPackageCoefficientIsUnit` states the resulting unit, not an extra hypothesis |
| Finite extension E of Q_l and its actual integers/quotients | `E : Type u`, `[Field E]`, `[Algebra (Padic C.l) E]`, `[FiniteDimensional (Padic C.l) E]`; `Padic.coefficientExtensionRing` |
| Positive finite exponent | `n : ℕ`, `hn : 1 ≤ n`; tower indices m mean exponent m+1 |
| Supplied operation datum | `S : SixFunctorOperationDatum D C E n hn`; finite, integral, rational and common-stage fields are reused |
| Separated finite-type schemes over k | `SixFunctorSpace D` and `[IsSeparated X.obj.hom]`; direct scheme formulations use `Over`, structure-map separatedness, local finite type and quasi-compactness |
| Morphisms over k, separated finite type | bundled arrows and their `hom.left`, or `[f.IsOver ...]`, `[IsSeparated f]`, `[LocallyOfFiniteType f]`, `[QuasiCompact f]` |
| Compactification and refinement | dependency's `Compactification f`, its recorded refinement-category arrows |
| Finite bounded constructible and finite-Tor domain | `sixFunctorFiniteCategory`; where required for finite coefficient change, `finiteTorConstructible ... K.obj` |
| Integral bounded constructible inputs | `sfIntegralConstructibleCategory`, retaining completeness and one common cohomological interval for all reductions; no added finite-Tor condition |
| Field presentations | `sfRationalConstructibleLocalization`, coefficient fields, actual `inclusion` and `stageSystem` |
| Specified inverse limits | retained products, `IsDerivedLimitTriangle`, `SfIntegralDirectImage`; these specify the presentation, not a hypothesis that the desired coefficient comparison is invertible |

All variables and universes are explicit; both auto-implicit options are false.
The finite categorical universes remain `u+2`. No extra universe equality is imposed.
Properness implies finite type and separatedness where used. Properness of the
base-changed map in an exchange square is derived from the square.

### Every clause of the statement

1. **Finite bounded-below witnessed domain and its coverage.**
   The main theorem uses `RefinementFiniteLevelOrigin`,
   `compactificationOriginCandidate`, and `refinementFiniteLevelFixedObject`.
   Its first conjunct supplies a witness and input isomorphism for every
   bounded constructible finite input. The subsequent natural isomorphisms
   range over the full recorded origin domain.
2. **Canonical refinement, identity, transitivity, independence, cocycle.**
   `theta` is pinned componentwise to `refinementComparisonIsomorphism`.
   The identity and composite equations concern that same theta. The comparison
   formula holds for every common refinement and the last equation is the
   three-target cocycle.
3. **Same normalized integral and field comparisons; compatibility.**
   `sfPackageCompactifiedTowerNormalizedReduction` uses actual chosen reduction
   maps, witnesses and the recorded finite refinement/composition maps.
   `sfPackageCompactifiedTowerStageCoherence` gives literal localization and
   inclusion formulas on these same comparisons, plus units and associativity.
   `sfPackageCompactifiedTowerFieldPassage` gives all enlarged field presentations.
   Witnesses for integral finite reductions follow from clause 1 applied to
   those constructible reductions. The same normalized-reduction theorem is
   universally quantified in the coefficient field, so it applies to every
   supplied coefficient-field stage.
4. **Integral ordinary and support reductions.**
   `sfPackageCompactifiedTowerIntegralReduction` asserts invertibility of the
   actual `sfDirectImageReductionComparison` and
   `coefIntegralCompactSupportComparison`; it also states integral membership
   of both outputs and the actual quotient-transition equation for support.
   There is no integral Tor assumption.
5. **Finite A_n to A_m.**
   `sfPackageCompactifiedTowerFiniteReduction` uses `1 ≤ m ≤ n`, finite
   constructibility and `hK` for finite Tor. It asserts invertibility of
   `finiteCoefficientChangeDirectImageMap` for the actual quotient factor
   homomorphism and `finiteLevelCompactSupportReductionComparison`.
6. **Normalized DVR reconstruction and common interval.**
   `sfPackageCompactifiedTowerEffectivity` states invertibility of the actual
   `normalizedDVRCounitComparison`, its equation for every longer quotient,
   and derived completeness. Only the final implication assumes constructible
   terms in one common `Set.Icc a b`, giving `sfIntegralConstructible`.
7. **Canonical composition, units, associativity, completed/field agreement.**
   The equations in `SfPackageCompactSupportCoherence` use the datum's own
   compositors. The associativity equation retains the `Category.assoc`
   compactification transport. Actual finite reduction of the integral
   compositor is in normalized reduction, and localization, inclusion and
   enlarged-presentation equations give field agreement.
8. **Proper identification and finite exchange.**
   `sfPackageFixedProperIdentity` constructs the actual identity-open unit
   comparison. `sfPackageFixedProperIdentification` uses that map and the
   recorded origin comparison at the same retained witness.
   `SfPackageFixedProperExchange` compares the actual ordinary and support
   exchanges for every presentation of the pulled-back witnessed input.
   `sfPackageCompactifiedTowerFiniteProperExchange` specializes to the actual
   positive quotient coefficients and the node's geometry.
9. **Integral strict quotient transitions and limits.**
   `sfPackageProperLevelComparison` is the actual finite identity-open map in
   the quotient coordinates. The first conjunct of proper transitions equates
   the two actual transition composites. Its second gives projection equations
   for the image of the datum's integral proper identity itself, via
   `sfPackageIntegralProperLimitIso` and `sfPackageIntegralSupportProjection`.
10. **Completed and field proper exchange and passage.**
    `SfPackageProperExchangeLaws` pins both proper identifications to the
    specified stage identifications and equates the actual
    `ExchangeProjectionStage.exchange` and `.compactExchange` composites.
    The higher theorem covers integral, rational, common-stage and every
    coefficient-field stage. Literal localization/inclusion formulas and the
    final conjunct of field passage carry the same proper identification to
    every field presentation.

### Dependency declarations read and used

| Recorded statement dependency | Imported module and declarations |
| --- | --- |
| `def-fix-six-functor-datum` | `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum`; its reexported `SixFunctorPushStage`, `SixFunctorHigherOperations`, `SixFunctorIntegralNormalization`, finite realization, finite origin comparison, witness support and compositor interfaces |
| `def-weil-compactifications-refinements` | `WeilConjectures.Compactification.RefinementCategory`: `Compactification`, its refinement category and identity-open compactification |
| `def-weil-integral-rational-qbar-compact-support` | `Sheaf.Paper.QcqsCompactSupportRealization`: normalized support realization; reexported actual integral value, chosen reduction and localization/common-stage constructions |
| `def-weil-pbc-etale-origin-witness` | `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`: `FixedEtaleOriginWitness`, its actual complex and isomorphism |
| `def-coef-normalized-dvr-tower` | `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`, its strict tower, evaluations, transition and restriction maps |
| `def-exchange-projection` | `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: `ExchangeProjectionStage.exchange`, `.compactExchange`, prescribed adjunction and compactification exchange formulas |

All six are public imports. Additional declarations used in signatures and
constructions are the finite refinement comparison from `CompactificationCoherence`,
the ordinary finite-coefficient map from `FiniteCoefficientDirectImage`, counit and
restriction maps from `NormalizedDVREffectivity`, reduction maps reexported by
`BasicOperationsCoefficientReduction`, and the fixed-scalar origin isomorphism from
upstream `LowerShriekIndependence`. Proof-dependency imports retain the node's
finite-origin, strict-calculus, completed-word/compactification-realization,
constructibility, coefficient-comparison, proper-coincidence and composition route.
The smaller upstream `WeilConjectures.CategoryTheory.StageSystem.Functor` supplies
common-stage descent; the broader old `PbcDescentFunctors` import also imported a
retired rational direct-image interface and is not needed by these statements.

### Edge cases

Empty schemes and zero inputs are permitted. Identity refinements and threefold
refinements have explicit equations. The quotient comparisons include m=n and m=1
and make no quotient-flatness assumption. Tower index zero is the first positive
quotient; no zeroth-exponent object replaces it. Effectivity permits unbounded and
nonconstructible normalized towers; its constructibility conclusion alone uses a
uniform interval. Integral inputs have no added finite-Tor assumption. The common
stage equations include identity field inclusions and arbitrary enlargements.
Every choice of retained finite witness is quantified; there is no selected
unrelated comparison. Proper limit and exchange statements concern derived
isomorphisms and actual maps, never only cohomology isomorphisms.

### Searches

The retained launcher log `searches.jsonl` records the original actual searches:

| Tool | Query | Result |
| --- | --- | --- |
| LeanFinder | Compactified direct-image towers have coherent refinement and composition comparisons compatible with coefficient reduction and proper direct image | Eight unrelated finite-type approximation/compact-open-cover hits; no package |
| LeanSearch | Proper compactification comparison isomorphisms coherent with coefficient reduction and derived inverse limits | Eight profinite-limit/abstract-completion hits; no package |
| Loogle | SheafOfModules.pushforwardComp, IsIso | Service rejected unqualified IsIso; no useful result |
| Loogle | CategoryTheory.Functor, CategoryTheory.NatIso | Service rejected NatIso; no useful result |
| Loogle | CategoryTheory.Functor.isoWhiskerRight | Twelve actual whiskering construction/coherence hits, reused |
| msearch Mathlib grep in CategoryTheory | compactification.*coher\|normalizedDVR\|compactSupport.*[Cc]omposition | No hits |
| Source/project rg | refinementComparisonIsomorphism, sfCompactSupportChosenReduction, coefIntegralCompactSupportComparison, supportProjection, directProjection, finiteCompositionNormalization, rationalModelNormalization, commonStageModelNormalization | Existing constituent interfaces above, reused |
| Repair rg in Mathlib, WeilConjectures and Sheaf | New integral-support/witness/composite reduction, integral proper-limit, common-stage transport and normalized-reduction/field-passage declaration names | No existing declarations |

No exact existing declaration states the whole package. The helpers express
components of this very node and reuse its existing notions; no independent new
mathematical notion is introduced.

## Second reading by Q12

This is the worker's own second pass, with the node, current blueprint, dependency
signatures and revised module open; the dispatcher explicitly prohibits spawning
another agent. Independent maintainer review remains required.

I checked the numbered return against the actual new signatures: the reduction
square's right side names the finite refinement/composition construction; its left
side uses the chosen projection adjunct. The generic field predicate no longer
accepts a coefficient-comparison record; its images are literal maps of the actual
localization/inclusion functors. Enlarged fields are quantified through the actual
stage-system functors and their presentation isomorphisms. The proper-limit
isomorphism is visibly built from the datum's integral proper identity and now
occurs in the projection equation. The unused strict-helper definition and the
independent existential proper-limit clause have been removed. The previously
correct reduction, effectivity, unit/associativity and exchange clauses remain.

The composite's scheme properties are supplied from the actual composition
instances, not as added assumptions. The chosen support projection has an explicit
source and target type. All theorem proofs remain sorry-only. Every declaration
has a blueprint/source docstring; theorem docstrings carry the corresponding proof
plan. The JSON signature is copied verbatim from the main theorem. A structural
comparison with the current read-clone node confirms that only `lean` changes.

### Validation

The repaired module passed `scompile.py` against the current live server sources:
39.9 seconds, two threads, the prescribed 60-second limit, no errors or warnings.
A local wrapper attempt reached its time limit; the wrapper's required server
confirmation passed. The final packet is also checked by `deliver2.py --no-push`.
The self-check verifies that only the node's `lean` field changes, its main signature
is verbatim, all 28 declaration names match the module, every line is at most 100
characters, and all 11 theorem proofs are sorry-only.
