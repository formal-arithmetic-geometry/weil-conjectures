## What changed

Implemented `CategoryTheory.AmbientCompletedTensor.ambientCompletedTensorAdjunction`
by composing the supplied derived tensor with the existing normalized quotient
presentation. On good representatives, the total tensor is K-flat and flat termwise;
the quotient computation and supplied tensor-model isomorphism give the required
comparison in the derived category of strict towers. Its chain-level balancing
normalization is isolated in `QuotientTotalTensorTowerComparison`.

Implemented `WeilConjectures.integralAmbientCompletedTensorAdjunction` by the existing
Roos/intrinsic completeness criterion and a proved categorical argument: if a functor
inverts its unit and the target unit is invertible, precomposition with the unit is
bijective. Surjectivity sends f to F(f) followed by the inverse target unit;
injectivity uses naturality after cancelling F(unit). The remaining integral
unit-inversion assertion is isolated in `IntegralCompletionUnitInverted`.

Added only private proof imports, local transparency annotations and proved private
helpers to the item. Existing
public signatures, definitions, public imports and the already-proved constructible
specialization are preserved. No other existing module is adapted. The item node's
proof and proof dependencies now describe this route. No definition or statement
change record is needed. The strict comparison retains its presentation isomorphism explicitly,
avoiding kernel reduction of identity maps on large total tensor data.

## Proved and sorry left

Two of the original three holes are closed by decomposition:

- `CategoryTheory.AmbientCompletedTensor.ambientCompletedTensorAdjunction`.
- `WeilConjectures.integralAmbientCompletedTensorAdjunction`.

The original hole still present is
`CategoryTheory.AmbientCompletedTensor.finiteTensorStep_existsUnique`, attached to
`lem-sf-ambient-completed-tensor-adjunction`. Its unique section formula still
determines the transition used by the actual tower definition.

Two holes are added, one in each new module:

- `CategoryTheory.AmbientCompletedTensor.quotientTotalTensorTowerComparison`, node
  `lem-sf-quotient-total-tensor-tower-comparison`.
- `WeilConjectures.IntegralOnSlice.integralCompletion_unit_inverted`, node
  `lem-sf-integral-completion-unit-inverted`.

This is a decomposition, not a net reduction in holes: two closed, two added, three
remaining across the packet. The general strict comparison contains no derived
localization, completeness, reflector or tensor-model choices. The integral helper
contains no tensor or complete target. Both are strictly smaller argument steps.
`WeilConjectures.integralConstructible_locallyComplete` was already proved and is
not counted as newly closed. All auxiliary private helpers are proved.

## No longer needed

No module is withdrawn or claimed globally unreachable. No existing public import
is removed. Exploratory imports of `IntegralTensorReductionTowerComparison` and
`IntegralTensorTransitionCompatibility` were not retained: their private levelwise
APIs do not directly provide the simultaneous general strict comparison.

The implemented ambient proof does not separately use these former planned proof
dependencies: `lem-pc-kflat-resolution`,
`lem-pur-kflat-change-of-rings-independent`, `lem-pur-derived-change-of-rings`,
`lem-weil-pbc-site-derived-tensor-descent`, and
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`. Good representatives and the
normalized quotient presentation already provide their required computations.
The separate `lem-weil-pbc-ringed-koszul-completion-reflector` application in the
item is replaced by the stronger unit-normalized `koszul_quotient_reflector` API
of `ConstantCompletionEquivalence`; the new integral unit-inversion node retains
that reflector as a mathematical proof dependency. These are route changes only;
existing source declarations and any other consumers are preserved.

## Where the brief, the DAG or earlier work was wrong

The initial source contains three holes despite the older change-record text
suggesting that all three tensor/adjunction declarations were proved. The actual
source and previous Q1 report were used as the baseline. No mathematical
statement or target is weakened.

The two library flatness predicates are not definitionally interchangeable: the
total-tensor model gives site flatness, while the quotient computation expects
monoidal flatness. The proved private helper transports exactness along
`siteSheafTensorRightIso` and converts independent K-flatness using the existing
equivalence. The normalized quotient presentation removes a second descent and
homotopy-limit construction from the item's proof.

The new strict statement was checked on zero complexes, the unit and zero ideals,
and arbitrary unbounded total degrees. Its balancing proof works without a
Noetherian hypothesis because it is a strict chain-level calculation. The integral
statement allows the empty scheme, zero object and unrelated universes; its source
argument uses the principal uniformizer datum and the small-site coefficient
universe max(u,t+1), not constructibility or a bound on the inputs.

## New nodes

`lem-sf-quotient-total-tensor-tower-comparison` is the balanced isomorphism of
strict quotient towers, with the exact section formula needed by the item. Its
inverse multiplies the two quotient scalar factors; the node records separately
the signed differential and successor-map calculations. The theorem is in
`Sheaf.Paper.QuotientTotalTensorTowerComparison`.

`lem-sf-integral-completion-unit-inverted` asserts that the actual integral
quotient-completion functor inverts its own specified quotient unit. The node
records the principal resolution, unit-preserving quotient/Koszul/Roos comparison,
and reflector inversion argument. The theorem is in
`Sheaf.Paper.IntegralCompletionUnitInverted`.

Both nodes carry three kinds of Mathlib search. Searches of the imported blueprint
for quotient tensor, completion unit and idempotent completion found no duplicate
of either precise statement. Existing project results were read first; the
constant-coefficient reflector and complete-target unit criteria do not state the
integral functor-map assertion. There are no change records because no existing
statement or definition changes.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
