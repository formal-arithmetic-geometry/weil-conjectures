## Worker report

Item: lem-pur-basic-realization-shift-square. Group: Q05. Stage: 2.

The new module is `Sheaf.SixFunctors.BasicRealizationShiftSquare`; its theorem is
`WeilConjectures.IntegralSystemRealization.basicRealizationShiftSquare`.
The only postponed proof is that theorem, whose docstring contains all eight
natural-language proof steps. Definitions contain actual terms or explicit
propositions about the existing constructions. No node statement was corrected.
No new mathematical construction, replacement coefficient system, or alternate
Roos functor is introduced.

The source was read in the current blueprint:
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/fix-prop-coherence.proof.md`,
the maps-used coefficient-comparison sentence. The node's detailed eight proof
steps supply the strict quotient and signed-cone formulation.

Hypotheses and clauses, in the order of the node:

1. The finite geometric field is `D : FiniteFieldDatum.{u}` and the prime is
   `l : ℕ` with `[Fact l.Prime]` and `_hl : l ≠ D.p`. The coefficient field is
   `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
   `[FiniteDimensional ℚ_[l] E]`. Valuation ring, uniformizer powers, and positive
   quotients are the existing coefficient-ring construction inside the imported
   calculus, not new parameters. Its natural-number level n means exponent n+1.
2. Finite-type k-schemes are `Over (Spec (.of D.k))` with
   `[LocallyOfFiniteType W.hom] [QuasiCompact W.hom]`. Geometric morphisms are
   morphisms in this over-category. Pullback adds `[IsSeparated v.left]`,
   `[LocallyOfFiniteType v.left]`, `[QuasiCompact v.left]`; proper image adds
   `[IsProper p.left]`; open extension adds `[IsOpenImmersion j.left]` and
   `[QuasiCompact j.left]`. All five operation/slot cases are present.
3. `Integral l E W` and `System l E W` are the existing ordinary unbounded
   derived categories of completed modules and strict quotient-semilinear
   systems on the small pro-etale site. Reduction is `(calculus l E W).reduction`
   and total limit is `coefficientSequenceLimit l E W`. The strict tower is
   `restrictedTower l E W`; the theorem uses the actual quotient comparisons
   `pullbackTensorPullbackTower` and `pullbackTensorTensorTower`.
4. The complete constructible integral input assumption is
   `GeneratorReduction.Admissible ... K lo hi torLo torHi`. Its definition
   includes `finiteTorConstructibleIntegral` and `SystemAdmissible` of reduction.
   Normalization, compatible etale origins, constructible cohomology, and the
   common finite cohomology/Tor intervals of intermediate systems are the
   explicit `GeneratorReduction.SystemAdmissible` hypotheses for each operation
   output. Both tensor inputs use the same four endpoints. These are reused
   predicates, with no private replacement for constructibility or completeness.
5. Every integer shift is explicitly quantified as `r : ℤ`. The cochain shift is
   Mathlib's `⟦r⟧`, so terms are reindexed by i+r and differentials acquire
   `r.negOnePow`. `basicRealizationSourceShift` composes the specified
   `reductionShift`, system-operation shift, and `limitShift` in that order.
6. The derived comparison maps are the actual maps:
   `GeneratorReduction.pullD`, `GeneratorReduction.tensorD`,
   `GeneratorReduction.integralPush` with identity comparison in its defining
   L S R coordinates, and `GeneratorReduction.openD`. The latter is defined in
   the imported generator module by the inverse open-reduction map and the
   inverse of the actual reconstruction unit. No arbitrary morphism parameter
   is substituted for these maps.
7. Strict simultaneous quotient representatives are stated for every good
   flat-term K-flat complex in `integralOperationsGoodComplex`.
   `BasicStrictPullSquare` fixes each reindexed unary component by equality to
   the identity (using HEq to retain the identified degree carriers) and states
   the square for `pullbackTensorPullbackTower` as an equality of tower maps.
   Thus quotient transitions, rather than only localized evaluations, occur.
   The direct-image case is the existing `BasicSystemImageShiftModels`, which
   uses a whole-system quasi-isomorphism into a K-injective resolution and its
   actual shifted resolution, with no assertion that evaluations are K-injective.
8. `BasicStrictTensorSquares` states the two strict tower squares simultaneously.
   Its system shifts satisfy `systemTensorLeftFormula` (coefficient 1) and
   `systemTensorRightFormula` (coefficient `(-1)^(r*i)`). The corresponding finite
   tower shifts satisfy `integralTensorLeftFormula` and
   `integralCompletedTensorFiniteShiftFormula`. The restricted source tower
   shifts are explicitly pinned by ordinary-reduction shift, these same system
   tensor shifts, and exact scalar restriction. The equations use the actual
   `pullbackTensorTensorTower` in either slot and are tower-map equations.
9. `BasicStrictOpenSquare` states that the actual
   `OpenSemilinearTensor.ordinaryChain` on Q[r] has exactly its degree-(i+r)
   component on Q. The supplied `Comparison` pins its ordinary map to the
   coefficient-generator formula and its localization to the specified `r`.
   The second conjunct spells out its augmented localization square on every
   flat-term K-flat Q using `Computation` and `c.kflat`. It is not an equality
   obtained by detecting equality after finite derived evaluation.
10. The Roos complex is the existing `CategoryTheory.roosF`, i.e. the shifted
    cone of 1-s. `BasicRoosShiftSquares` requires an entire coherent shift `cs`
    satisfying `RoosConeCalculus.ShiftFormula`. That formula fixes the unshifted
    product coordinate with coefficient 1 and the shifted coordinate with
    coefficient `r.negOnePow`, exactly chi(b,a)=(b,(-1)^r a).
11. The next conjunct of `BasicRoosShiftSquares` is the strict-chain equality
    `roosF.map (f⟦r⟧') ≫ chi_Y = chi_X ≫ (roosF.map f)⟦r⟧'` for every tower
    chain map f. It therefore applies in particular to all preceding comparison
    diagrams and both tensor-slot squares after the explicit signed tower
    identifications. Naturality belongs to the same `cs`, not another cone map.
12. Its last conjunct transports through every
    `PrimitiveCounit.RoosRealization` with its actual normalized comparison to
    `coefficientConstantTowerLimit`. The equation includes the localization
    shifts and the canonical right-derived limit shift
    `basicConstantLimitShift`. `RoosRealization` fixes rho by its K-injective
    augmentation/projection normalization; no arbitrary natural isomorphism is
    used. Together with exact `restrictedTower` this gives the actual total
    limit morphism square, including semilinear scalar restriction.
13. `BasicDerivedRealizationSquares` contains pull, proper, shriek, and the two
    tensor-slot equations. `BasicRealizationSquare` is literally
    `d (K⟦r⟧) ≫ sigma_G = sigma_F ≫ (d K)⟦r⟧'`, the node's displayed identity
    in Lean's left-to-right composition convention. Target shifts are exactly
    `(integralShifts l E).pull`, `.shriek`, the defining proper composite, and
    `(tensorShifts l E).integralLeft` / `.integralRight`.
14. Its `reconstruction` field explicitly states
    `Adjunction.CommShift.CompatibilityUnit` for `(calculus ...).adjunction`,
    the prescribed `reductionShift` and `limitShift`. Thus the unit in the
    open formula is the actual shift-compatible unit of the same adjunction.
15. `pull_natural`, `open_natural`, and `tensor_natural` give the actual derived
    input-morphism equations; proper naturality is the identity transformation
    of the defining L S R functor. All chain-model assertions quantify over
    every good representative (and all resolution maps in the proper model),
    rather than picking an unrelated finite comparison. The final equations
    use fixed functors/maps and all integral derived objects satisfying the
    hypotheses; they contain no representative parameter. They are therefore
    independent of these model choices. Every final equality is in the whole
    integral derived category, not a cohomology or reduction-level surrogate.

Dependency declarations used:

- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`,
  `CoefficientDerivedSystemCalculus`, and its reduction/adjunction/normalized
  model data. Its actual data is reused via `IntegralSystemRealization.calculus`.
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`:
  `WeilConjectures.IntegralSystemRealization.integralCompactificationSystemRealization`,
  `Operations`, `Realizations`, and the actual system operations.
- `Sheaf.SixFunctors.IntegralOperationShiftData`:
  `systemPullShift`, `systemPushShift`, `systemOpenShift`, `tensorShifts`,
  `integralShifts`, `reductionShift`, `limitShift`, `restrictedTower`,
  `levelRestriction`, and the left/right system and integral tensor formulas.
- `Sheaf.SixFunctors.GeneratorReductionStatement`:
  `WeilConjectures.GeneratorReduction.Operations`, `Admissible`,
  `SystemAdmissible`, `pullD`, `tensorD`, `integralPush`, `openD`, `openDInv`,
  `primitiveReductionTranspose`, and `generatorReductionCoherence`.
- `Sheaf.Paper.CompletedPrimitiveCounitComparison`:
  `WeilConjectures.PrimitiveCounit.RoosRealization`, `Comparisons`, and
  `completedPrimitiveCounitComparison` for the normalized actual realization.
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`:
  `WeilConjectures.IntegralOpenReduction.Operations`, `TensorComparison`,
  `extension`, `J`, and `systemExtension` for the actual open coefficient map.
- `Sheaf.CategoryTheory.StrictRoosComparison`:
  `CategoryTheory.strict_roos_comparison`, the normalized bridge used in the
  proof and in the existing `RoosRealization` interface.
- `Sheaf.Paper.PurReductionLimitShiftAdjunction`:
  `WeilConjectures.PurReductionLimitShiftData`, its `unit_shift`, and
  `purReductionLimitShiftAdjunction` for the actual reconstruction-unit step.
- Added already-landed statement dependency
  `def-pur-completed-pullback-tensor-comparison`:
  `Sheaf.Paper.CompletedPullbackTensorComparison`,
  `WeilConjectures.pullbackTensorOrdinaryReduction`,
  `pullbackTensorPullbackTower`, and `pullbackTensorTensorTower`.
- New existing:true statement definition owner
  `def-pur-basic-system-image-shift-models`:
  `Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus`,
  `WeilConjectures.IntegralSystemRealization.BasicSystemImageShiftModels`
  and `basicSystemImageResolutionIso`. Its theorem remains a proof dependency.
- Already-landed statement dependency `def-sf-open-semilinear-tensor-model-data`:
  `Sheaf.SixFunctors.OpenSemilinearTensorModel`,
  `WeilConjectures.OpenSemilinearTensor.Comparison`, `Computation`,
  `OrdinaryReduction`, `ordinaryChain`, and `extensionComplex`.
  The existence theorem remains a proof dependency.
- New existing:true statement definition owner
  `def-pur-roos-coordinate-shift-formula`:
  `Sheaf.Algebra.Homology.RoosConeCalculus`,
  `CategoryTheory.RoosConeCalculus.ShiftFormula`, with its coordinate helpers.
  Its theorem conclusion is not used in the statement.
- Already-landed statement dependencies `def-a1-flat-term-kflat-complex` and
  `def-a1-integral-finite-pullback-tower`: respectively
  `WeilConjectures.integralOperationsGoodComplex` and
  `integralOperationsPullbackTowerFunctor` in
  `Sheaf.Paper.IntegralOperationsWellDefined`.
- New existing:true statement definition owner
  `def-pur-integral-finite-tensor-tower`:
  `WeilConjectures.integralOperationsTensorTowerFunctor`, with its finite-level,
  pure-tensor-generator and actual quotient-transition helpers, in
  `Sheaf.Paper.IntegralOperationsWellDefined`.
- New existing:true statement definition owner
  `def-pur-integral-finite-tensor-right-shift-formula`:
  `WeilConjectures.integralCompletedTensorFiniteShiftFormula` in
  `Sheaf.SixFunctors.CompletedTensorShiftRight`.

The remaining recorded proof dependencies are imported plainly, including
K-flat resolution independent of coefficients, quotient-system flat models,
shifted sequence K-flat and K-injective models, injective Roos shifts,
flat-Roos descent and exact countable pro-etale products. No downstream
`IntegralBasicOperationShift` module is imported; that would create a cycle.

Edge cases checked before writing and on rereading:

- r=0 gives coefficient 1 in both tensor slots and both cone coordinates.
- r=1 and r=-1 both negate the shifted cone coordinate; the right tensor sign
  still depends on first degree i, including negative i. There is no natural
  number restriction on r or i.
- Zero complexes and empty schemes remain permitted; no nonzero or nonempty
  hypothesis was added. Empty finite intervals cannot satisfy the existing
  admissibility predicate; valid endpoints are not fixed numerically.
- Quotient level 0 in Lean is the first positive quotient, not a discarded
  zero-th quotient. All transition equations are natural-transformation equations.
- Tensor input slots are separate, rather than changing both inputs at once.
- Proper-image resolutions are simultaneous system resolutions, and scalar
  restriction is followed by the actual limit construction; neither operation
  assumes evaluated K-injectivity or inverse-limit preservation by j_!.
- The final fields are equations of actual derived morphisms; no use of
  conservativity/faithfulness of finite evaluation is hidden in their statement.

Searches performed (the msearch wrapper records the calls):

- leanfinder, `Strict quotient system realization comparisons commute with
  cochain shifts and normalized Roos cone signs`: eight generic mapping-cone
  results, no statement fixing the required quotient comparisons and d_A.
- loogle, `CochainComplex.mappingCone.shiftIso, CategoryTheory.NatTrans.CommShift`:
  no results.
- grep in Mathlib/CategoryTheory,
  `realization.*[Ss]hift|[Rr]oos.*[Ss]hift`: no results.
- leansearch, `strict quotient coefficient realization commutes with shifts and
  normalized Roos cone naturality`: eight generic quotient/shift results,
  no exact match.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for Roos/realization shifts
  located the existing generic cone calculus, operation shift data and the
  downstream basic-operation theorem. None states this node's simultaneous
  strict quotient squares and normalized realization. Literal item-id search
  in `lean/WeilConjectures` found no declaration.
- rg for every new declaration name in `dag/lean_names_upstream.json`, Mathlib,
  `lean/WeilConjectures`, and `lean/Sheaf` found no collision.

No STATEMENT-DISPUTED claim or dependency-interface fault was found. The node's
statement and proof are unchanged. The repaired stmt_deps gains the four landed
definition nodes and four existing:true definition owners listed above. Its
proof_deps is preserved verbatim from live main; the basic-system and open-model
theorems remain there. No dependency-interface repair is needed.

Validation: prescribed scompile.py checked both the isolated sandbox module and
its intended library module cleanly, with no errors or warnings.

## Second reading by Q05

This is a separate self-reading with the node and module open, not a claim of
another worker's review. The dispatcher's explicit instruction prohibits
starting another agent, and the delivery is reserved for the maintainer's
independent review.

I compared all clauses again using the mapping above. This caught and repaired
an overly general Scheme quantifier in the open/Roos conclusion: the delivered
main theorem now uses finite-type schemes over the fixed D.k throughout. It
also prompted the explicit `reconstruction` field for the actual adjunction
unit, rather than leaving its shift compatibility only in the proof plan.
The strict tensor square uses the two distinct signed identifications and the
same whole-tower maps; the Roos formula has coordinates (b,a), with signs
(1,(-1)^r). The proper field uses the defining integralPush coordinates, while
the open field uses the actual inverse-unit formula in openD. No omitted
finite-transition clause, input slot, complete/Tor hypothesis, or replacement
comparison was found on this pass. The final equations precede any cohomology
or evaluation and use exactly the imported comparison maps.


## Repair of return H2 (immutable head 0b498621b411)

The maintainer found theorem-node additions to stmt_deps although the signature
uses only plain definitions from their modules. I refreshed the item node's
unchanged fields from current main and retained the reviewed Lean record. Main
has no Lean record for the item; its statement, proof, proof_deps and nine original
stmt_deps match the retained delivery. The wrapper rebases the repair package on
current main when constructing the delivery commit.

The repair removes the three rejected additions
`lem-pur-basic-system-shift-resolution-calculus`,
`lem-sf-open-semilinear-tensor-model`, and `lem-pe-roos-cone-calculus` from the
consumer's added stmt_deps. The original statement-dependency list is retained.
It substitutes the already-landed `def-sf-open-semilinear-tensor-model-data`, and
adds existing:true definition owners for the image-resolution shift-model
predicate and the Roos coordinate shift predicate. It also cites the two
already-landed definition owners explicitly requested in the return,
`def-a1-flat-term-kflat-complex` and `def-a1-integral-finite-pullback-tower`.
The return's remaining ownership gap is repaired with existing:true definition
nodes for the finite tensor tower and its signed right-slot formula.

The theorem nodes already in proof_deps, including the basic-system and open
model theorems, are retained there. The new Roos owner refers only to the plain
ShiftFormula definition, without asserting the roos_cone_calculus theorem.
No source import is altered: the same modules supply their public definitions
and remain available for the recorded proof plan. No Lean declaration, signature,
proof, or data was changed in this repair. The advisory proper-image conjunct
is retained in its reviewed defining coordinates as requested.

The unchanged Lean file has SHA256
`d84082b117c5d461011021edc7310aa1ede99138702f2610e7f8d2094a8ceae2`.
The prescribed scompile.py check again succeeds for sandbox and intended library
module with no errors or warnings. The four new definition records all point to
published modules with existing:true, omit lean.file, and reproduce the actual
existing declaration signatures verbatim.

## New nodes

`def-pur-basic-system-image-shift-models` owns the already-published
`BasicSystemImageShiftModels` and `basicSystemImageResolutionIso` in
`Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus`. Its TeX introduces the
actual universal-derived-unit computation c_a on every whole-system K-injective
resolution and defines the prescribed shift-square property, with no existence
assertion. Its source is the current blueprint coefficient-comparison sentence,
item proof step 1, and Stacks 011G/070I/079P/07A6. The node cites the existing
operation, shift, quasi-isomorphism, K-injective and derived-category definitions.
No prior definition node owns these plain helpers; the theorem node previously
listed them only as auxiliary declarations. This is definition ownership, not
a second Lean definition.

`def-pur-roos-coordinate-shift-formula` owns the already-published
`CategoryTheory.RoosConeCalculus.ShiftFormula` and the pi/v/ucoord coordinate
helpers in `Sheaf.Algebra.Homology.RoosConeCalculus`. For an abelian category with
countable products and a supplied coherent shift, its two projection equations
are exactly (b,a) mapped to (b,(-1)^r a). It asserts no existence or limit bridge.
Its source is Stacks 011G/014E and the item proof step 4, with the existing strict
Roos functor and triangulated-shift definitions as dependencies. No definition
node owns this predicate; the Roos calculus theorem is a different assertion.

`def-pur-integral-finite-tensor-tower` owns
`WeilConjectures.integralOperationsTensorTowerFunctor` with TensorLevel,
TensorSection, TotalTensorSection, TensorTransition and its unique-generator
characterization in `Sheaf.Paper.IntegralOperationsWellDefined`. Its TeX records
ordinary finite reductions, direct-sum total tensor, restricted scalar action,
and the actual transition sending x tensor y to the tensor of their quotient
images. Its source is Stacks 012Z/06YT/03EK and item proof steps 1-2. No flatness,
K-flatness or boundedness restriction is introduced, and coefficient and scheme
universes remain independent. Existing coefficient, reduction, cochain, total
tensor, sheaf tensor and scalar-restriction definitions are cited. The existing
pullback-tower owner does not own this two-input tensor-tower construction.

`def-pur-integral-finite-tensor-right-shift-formula` owns the already-published
`WeilConjectures.integralCompletedTensorFiniteShiftFormula` in
`Sheaf.SixFunctors.CompletedTensorShiftRight`. Its TeX defines the formula for a
supplied strict-tower isomorphism: the (i,j) source summand goes to the
(i,j+r) target summand with coefficient (-1)^(ri), using the inverse target
cochain reindexing. Its source is Stacks 011G/012Z and item proof step 2.
It cites the new finite tensor tower owner and the existing shift definition.
It is a predicate, not the existence theorem CompletedTensorFiniteShift or the
derived completed-tensor shift theorem; neither theorem has been duplicated.

For each of these four nodes I ran the same combined searches through msearch.py:
LeanSearch and LeanFinder query `Strict finite coefficient tensor tower, signed
right tensor shift formula, Roos cone coordinate shift formula, and simultaneous
direct image resolution shift models`; and Mathlib grep query
`BasicSystemImageShiftModels|integralOperationsTensorTowerFunctor|integralCompletedTensorFiniteShiftFormula|RoosConeCalculus`.
LeanSearch returned eight generic cochain/cone shifts, including
mappingCone.shiftIso and mappingCone.shiftTriangleIso. LeanFinder returned eight
generic tensor/shift/Tor interfaces including HasGoodTensor and CommShift2Setup
integer signs. Mathlib grep returned zero hits. Exact returned declaration names
are recorded in each node's mathlib_searches. Project rg found the four existing
interfaces in the four modules named above and no matching declaration in
lean/WeilConjectures. A declaration-ownership scan of all definition-node Lean
records found no existing definition owner for the four interfaces. The four
blueprint_refs.py name searches each returned zero matches. Thus the searches
support reusing existing code and adding definition ownership only.

On a second self-reading of this repair, I checked every definition node against
its existing declaration body. For the image model the equation contains both
localization shifts and the inverse actual derived-unit computation; for Roos
the unshifted coordinate has sign 1 and the shifted one (-1)^r; for the tensor
tower both inputs' actual quotient transitions are retained; for the right
formula the exponent uses the first input's degree i. These descriptions impose
no geometric or completeness hypothesis absent from the definitions. The
consumer's reviewed mathematics is unchanged, and its added definition
ownership replaces every theorem-only ownership gap named in H2.
