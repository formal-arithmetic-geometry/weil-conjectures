## Worker report

Q113 states `WeilConjectures.spNormalizedArithmeticInterpolation` in
`Sheaf.Paper.NormalizedArithmeticInterpolation`. No proof is supplied. The named
auxiliary theorems also have `sorry` proofs and complete proof plans in their docstrings.
The node's mathematical statement and proof text are unchanged. The H2 repair below
adds the three landed declaration-owning nodes to `stmt_deps`.

The source was reread in the current blueprint, not its historical snapshot:
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/sk-lem-sp-tower-equivalence.proof.md`,
Counit paragraph. The node elaborates that paragraph's arithmetic interpolation
and uniformizer reconstruction, as described in its four proof steps.

### Hypotheses and objects

* The prime is `(l : ℕ) [Fact l.Prime]`; the finite coefficient extension is
  `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  The existing coefficient construction chooses its valuation ring and uniformizer;
  `spInterpolationRings` abbreviates the actual `coefficientSequenceCommRingSystem`,
  with the original quotient maps. There is no separately chosen tower of rings.
* The scheme is `(W : Scheme.{t})`, and invertibility is the explicit hypothesis
  `_hl : IsUnit (l : Γ(W, ⊤))`. Its pro-etale site is `Scheme.ProEt.topology W`.
  Site objects have universe `t+1`, morphisms universe `t`; coefficients and module
  sections have size `max u (t+1)`. Neither `u=t` nor an equality with `t+1` is imposed.
  The essentially-small site framework already used by the dependencies supplies
  the small-model interpretation; this delivery does not introduce another site.
* `B_k` in the node means positive exponent `k`. The existing finite coefficient API
  instead indexes exponent `k+1` by `k : ℕ`. Therefore
  `spInterpolationIndex e he n = e*(n+1)-1`. The strict-increase helper states precisely
  the positivity consequence needed for this order embedding.
* `e : ℕ` and `he : 1 ≤ e` are exactly the arithmetic-step hypothesis.
* `spInterpolationSystems` uses the recorded `StrictRingSystem` and
  `selectedSystemRings`; `N` is in its ordinary `DerivedCategory`. There is no bounded,
  constructible, finite-Tor, or cohomological-amplitude restriction.
* `L : SystemLevelLeftExtensionTheory` and `S : CoefficientDerivedSystemCalculus`
  are the specified dependency constructions, with their canonical representative
  and adjunction normalizations, not new mathematical hypotheses on `N`. Their
  existence is the content of the recorded dependency theorems. Quantification over
  their specified models avoids a new private copy or uncharacterized choice.
* `_hN : SpInterpolationNormalized ... N` quantifies over **all** inequalities
  `h : n ≤ m`. Its morphism is `(systemDerivedTensorAdj ... h).homEquiv.symm` of
  `(L.transition ... h).app N`, so it asserts invertibility of the actual transition
  adjunct, with the direction and finite coefficient categories of the node.

### Clauses of the conclusion

The output structure packages the following assertions about the fixed object
`F = (L.selected B r).derived.obj N`; it does not existentially substitute another F.

1. `ceiling` identifies `systemNextSelected r k` with `k/e`. On positive indices this
   is exactly `ceil((k+1)/e)-1`, including the initial block before exponent `e`.
   `evaluation` is the tensor formula for every level, and `evaluation_eq` pins it
   to the natural transformation `L.selectedDerivedBelow`. Thus the displayed
   identifications are natural evaluations of the existing derived left extension.
2. `unit_isIso` is invertibility of the **actual** adjunction unit `N → UF`.
   The `UF ≅ C` used here is its inverse as a map of derived strict systems, so it
   automatically identifies every selected transition. `selectedEvaluation_eq`
   explicitly fixes the evaluated identification to `spInterpolationSelectedEvaluation`,
   formed from that inverse unit and the identity-on-sections presentation comparison.
3. `adjacent` writes the actual adjacent transition adjunct of F as the composite
   in `L.selectedTransition`: evaluation, canonical tensor associators, base change
   of the actual selected transition adjunct, and inverse evaluation. The selected
   inequality is `systemNextSelected_mono r k`. If its endpoints agree, the existing
   theory's `transition_identity` and tensor unit normalization make this the identity
   transition; the formula does not introduce an arbitrary isomorphism for that case.
4. `normalized` quantifies over every `n ≤ m`, not just consecutive levels.
   `sequence_normalized` expresses the same normalized system in the existing
   ringed-sequence presentation used by reconstruction. This retains identities and
   strict composition; scalar forgetting is the dependency's strict tower, not a
   collection of unrelated derived-level maps.
5. `SpInterpolationForgetting` fixes scalar forgetting on finite levels by **equality
   of ordinary evaluation functors**, and fixes all horizontal maps by their actual
   section functions. Its exactness permits termwise passage to the ordinary unbounded
   derived category. `spInterpolationLimit` is its composition with the existing
   `coefficientConstantTowerLimit`, the total right derived inverse-limit functor.
   This is M, without assuming exactness of sheaf products.
6. The full scalar-forgotten F and its total limit use the existing
   `coefficientSequenceRestriction`, `coefficientSequenceDerivedRestriction`, and
   `coefficientSequenceLimit`. `restrictionSquare` and `restrictionSquare_sections`
   identify arithmetic selection with termwise scalar forgetting by the ordinary
   identity on sections. `spInterpolationRestrictionSquare` localizes that very square.
7. `arithmetic` is a natural isomorphism from total limit to total limit after the
   recorded `StrictTowerArithmetic.derivedRestriction`. `arithmetic_rep` fixes it on
   simultaneous K-injective representatives to `StrictTowerArithmetic.limitMap`,
   the ordinary restriction of compatible families. The arithmetic-restriction
   dependency supplies such simultaneous resolutions, so this is the canonical
   map, not a comparison chosen after evaluating one object.
8. `limitIso` is `L_B F ≅ M`. `limitIso_eq` fixes its hom to arithmetic restriction,
   followed by total limit of the scalar-forgotten **inverse unit**. `projection`
   equates its composite with the actual nth projection of M to the projection of
   F at `e*(n+1)-1`, followed by restriction of the fixed selected evaluation.
   `spInterpolationProjection` is built from the recorded total-limit projection and
   exact-localization evaluation comparison.
9. `spInterpolationCounit` is a single map of derived selected strict systems. It
   restricts the actual `S.adjunction.counit`, precomposes with reduction of
   `limitIso.inv`, and postcomposes with the inverse arithmetic unit, transporting
   through the existing strict-system/ringed-sequence equivalence. `counit_isIso`
   asserts that this very map is invertible.
10. `spInterpolationReductionEvaluation` identifies its source at n with the recorded
    `coefficientFiniteDerivedExtension ... (r n) M`, using `S.reductionEvaluation`.
    `counit_evaluation` identifies each component of the **one system map** with the
    scalar-extension adjunct, under `coefficientFiniteAdjunction`, of the actual
    `spInterpolationProjection`. `finite_isIso` asserts invertibility of these actual
    adjuncts. These are precisely `M ⊗^L_A B_{e(n+1)} → C_(n+1)`, coherent in the
    derived category of strict selected systems.

All helper definitions have actual data. The identity-on-sections ordinary evaluation
comparison uses a named **unique** existence theorem: both evaluations have the same
section modules, identity maps give the comparison, and section faithfulness gives
uniqueness. This determines the object completely; no arbitrary existence choice is
used. The arithmetic embedding uses a named strict-monotonicity theorem only for its
proof field. Both helpers and the main theorem are listed in `lean.declarations`, carry
this node's blueprint tag, and state their natural-language proofs in their docstrings.

### Dependency declarations used

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the publicly reexported
  `Padic.coefficientExtensionRing` construction. These are used through the existing
  integral coefficient sheaves, not reimplemented.
* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its reexports:
  `integralCoefficientCommRingSheaf`, `integralCoefficientSheafSystem`,
  `completedIntegralCommRingSheafUnrestricted`, and their actual projections.
* `Sheaf.CategoryTheory.SystemLevelLeftExtension` and its public basic/scalar modules:
  `SheafOfModules.systemLevelLeftExtensionTheory`, `SystemLevelLeftExtensionTheory`,
  `StrictRingSystem`, `selectedSystemRings`, `systemSubsequence`,
  `derivedSystemSubsequence`, `derivedSystemEvaluation`, `systemDerivedTensorAdj`,
  `systemNextSelected`, and the theory's selected/evaluation/transition/tensor fields.
* `Sheaf.Paper.NormalizedDVRTower` (reexported by the coefficient calculus):
  `normalizedDVRDerived`, the actual quotient restrictions and their derived categories.
  Its `NormalizedDVRTower` combines these same finite levels, adjoint normalization,
  scalar-forgotten tower and transition coherence. We keep the original
  strict-system datum and its scalar-forgetting functor instead of adding its extraneous
  finite-field bookkeeping parameter as a hypothesis on the present arbitrary scheme.
* `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`, the recorded
  total derived limit and canonical projection framework. Its specialization already
  used by the calculus is `coefficientConstantTowerLimit` and
  `coefficientConstantTowerProjection`.
* `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus`, `CoefficientDerivedSystemCalculus`,
  `IsNormalizedCoefficientSequence`, `coefficientSequenceDerivedEvaluation`,
  `coefficientSequenceLimit`, `coefficientSequenceProjection`,
  `coefficientFiniteDerivedExtension`, `coefficientFiniteDerivedRestriction`,
  `coefficientFiniteAdjunction`, and the calculus's actual reduction/counit/evaluation.
* Presentation transport uses the existing `strictSystemSequenceEquivalence` and
  additivity instances reexported by
  `Sheaf.CategoryTheory.SystemSingletonScalarExtension`; it introduces no new
  category of systems.
* Proof dependencies were read and imported:
  `Sheaf.CategoryTheory.StrictTowerArithmeticRestriction`, theorem
  `CategoryTheory.StrictTowerArithmetic.strictTowerArithmeticRestriction`, and its
  public definitions `restriction`, `derivedRestriction`, `complexRestriction`,
  `limitMap`; `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`, theorem
  `WeilConjectures.purNormalizedReconstruction`. Scalar restriction is Mathlib's
  `SheafOfModules.restrictScalars` throughout.

### Edge cases checked before finalizing the statement

* `e=1`: r is the identity on predecessor indices; next selected index is k, the
  formulas reduce to tensor with the same coefficient ring, and the comparison is
  the dependency's actual identity arithmetic restriction.
* `e=2`: levels 0 and 1 both select C_0 over exponent 2; the next block selects C_1
  over exponent 4. The block-crossing transition uses C_1 to C_0; the within-block
  transition uses the identity. This checks the ceiling and map directions.
* The smallest positive exponent, each exact multiple of e, and both sides of a
  block boundary are included. `e=0` is excluded by exactly `he`, as in the node.
* Equal indices in the normalization quantifier use actual identity transitions;
  nonadjacent pairs are explicitly quantified, not inferred from an omitted clause.
* The zero system and the empty scheme are allowed. No nonzero-object, nonempty-site,
  finite-field-base, or finite-dimensional-cohomology assumption is added.
* Arbitrary independent coefficient and scheme universes remain allowed; no site
  universe is collapsed. All complexes and derived categories remain unbounded.
* Maps to evaluated finite objects alone do not specify a coherent derived-system
  comparison; the single `spInterpolationCounit` and its evaluated equality were
  therefore included explicitly.

### Searches for an existing statement

All searches were made with the prescribed wrapper/read-only sources.

* `msearch.py ... leanfinder` with
  `Derived normalized module systems over DVR quotients interpolate along arithmetic subsequences and their actual counit reductions are isomorphisms`:
  eight ordinary completion/`IsAdicComplete.StrictMono` hits, no varying-sheaf-ring
  derived strict-system interpolation or coherent actual counit statement.
* `msearch.py ... loogle` with
  `CategoryTheory.Functor.IsLeftDerivedFunctor, IsAdicComplete.StrictMono.extend`:
  zero hits.
* `msearch.py ... grep` with
  `normalized.*(system|tower)|arithmetic.*(restriction|subsequence)`:
  three unrelated `Mathlib/FieldTheory/NormalizedTrace.lean` hits.
* `msearch.py ... leansearch` with
  `Derived normalized coefficient systems along arithmetic subsequences actual counit isomorphisms`:
  eight generic adjunction/derived-counit hits; none states this assertion.
* `rg`/item-id searches in `lean/WeilConjectures` and searches for
  `normalizedArithmeticInterpolation|normalized_arithmetic_interpolation` in
  `lean/Sheaf` and the upstream library found no existing declaration.
  Broader arithmetic/normalized/strict-system searches found the dependency
  constructions above; these have been reused. Their general left-extension theorem
  alone does not state normalization preservation, the canonical limit comparison,
  or the selected coherent actual reconstruction counit.

No `STATEMENT-DISPUTED` issue was found. No source correction, new node or dependency
repair is needed. No live repository file or launcher script was edited.

## Second reading by Q113

The dispatcher explicitly prohibits starting another agent and says the maintainer's
independent review reads this delivery. Consequently this section records a second pass
by the assigned worker, not a falsely claimed independent-agent review.

I reopened the node and module and matched: prime/extension/scheme/invertibility to the
explicit context; positive arithmetic exponents to `e*(n+1)-1`; every-pair normalization
to `SpInterpolationNormalized`; the fixed F to `L.selected.derived`; the natural tensor
formula to `evaluation_eq`; the selected system identification to the actual unit;
the adjacent map to its full associator formula; all-pair output normalization to
`normalized`; the strict scalar-forgotten tower and total limits to the existing
exact-localization/Rlim API; canonical arithmetic restriction to its representative
normalization; projections to `projection`; and actual finite reduction comparisons
to the components of `spInterpolationCounit`, not separately chosen isomorphisms.

This pass removed the possibility of an unspecified evaluated comparison by fixing
selected evaluation to the inverse actual unit. It also made the adjacent associator
formula explicit and fixed the arithmetic limit isomorphism to the ordinary restriction
map on K-injective representatives and then total limit of that inverse unit. The
identity-on-sections ordinary presentation comparison is uniquely characterized before
being chosen. I checked initial and repeated-index blocks, `e=1`, empty W, zero N,
independent universes, and nonadjacent transitions against the same node text. These
are elaborations of its maps, not changes to its statement or additional hypotheses.

### Validation

The delivered module compiled cleanly through the prescribed `scompile.py`, including
its library-module compile (33.8 seconds); there were no errors or disallowed warnings.
Only the three named theorem proofs are postponed. Generated unused structure size/injectivity
helpers are disabled to keep the exact statement within the per-file compile budget.

## Repair of returned delivery 4598299f1444

The maintainer's H2 finding is repaired by adding exactly these three already-landed
nodes to `stmt_deps`, as authorized by brief-stage2 §5 (STMT_DEPS MAY GAIN LANDED NODES):

* `def-sp-strict-tower-arithmetic-restriction-data` owns
  `CategoryTheory.StrictTowerArithmetic.restriction`, `derivedRestriction`,
  `complexRestriction`, and `limitMap` in
  `Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs`. These occur in the
  restriction square, arithmetic comparison, and representative normalization.
* `def-pur-system-level-left-extension-basic` owns `StrictRingSystem`,
  `SystemLevelLeftExtensionTheory`, `selectedSystemRings`, `systemSubsequence`,
  derived system evaluation/restriction, tensor/adjunction, and next-selected-index
  data in `Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic`. These type the
  input system and its evaluation, normalization, and actual transition formulas.
* `lem-pur-system-ringed-sequence-site` owns `strictSystemSequenceEquivalence`
  in `Sheaf.CategoryTheory.SystemRingedSequenceSite`. That exact equivalence types
  the limit and selected-evaluation comparisons, sequence normalization, and counit.

I compared the retained sandbox record against the current read-only main record and
read these three nodes' landed Lean records. The original eight statement dependencies
are retained. The repair changes `stmt_deps` in the node and updates this report;
the Lean record retains its recorded delivery metadata, and the Lean module is byte-for-byte retained. No new node,
source correction, or dependency interface repair is involved. The maintainer's
independent review of the returned immutable head checked the mathematics clause by
clause and accepted the strict forgetting tower with `IsNormalizedCoefficientSequence`
as the rendering of the normalized DVR tower datum.
