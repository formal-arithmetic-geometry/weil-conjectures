## What changed

Replaced the sorry in `WeilConjectures.IntegralSystemRealization.integralOpenFiniteEvaluation`
with a complete adjunction calculation. The private `assemble` lemma cancels the inverse open
finite-evaluation isomorphism, transposes under the finite open adjunction, uses the two
inverse-mate unit equations, and combines pullback evaluation, reduction naturality and the
scalar open-unit equation. The existing theorem signature and `openFiniteReduction` definition
are unchanged.

Added `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare` and
`Sheaf.SixFunctors.IntegralOpenScalarUnitSquare`. The former constructs
`integralFiniteScalarPull` by transporting the existing `PurCompactSupport.scalarPull` through
`finiteReductionIso` and the derived `finitePullbackIso`; there is no new choice or holed data.
The two new theorems isolate the distinct geometric normalizations that the original proof
paragraph had combined. The item has one private proof import of the scalar-unit module;
that module publicly imports the pullback-square module because its statement uses the
constructed scalar/pullback comparison.

Validation: both new modules compiled in the ordered sandbox compile. The final assigned
module then compiled successfully against those sandbox artifacts (`lcompile.py`, exit 0,
6.1 seconds), with no warnings. The existing definition and theorem signature were also
checked textually against the current shared source.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralSystemRealization.integralOpenFiniteEvaluation`
(node `lem-sf-integral-open-finite-evaluation`). Its assembly proof is complete.

Added exactly two holes, each in a named public theorem in its own module:

- `WeilConjectures.IntegralSystemRealization.integralReductionPullFiniteSquare`
  (`lem-sf-integral-reduction-pull-finite-square`). This is finite evaluation of the
  normalized whole-system pullback model, for an arbitrary morphism. It contains no open
  extension or open-reduction mate.
- `WeilConjectures.IntegralSystemRealization.integralOpenScalarUnitSquare`
  (`lem-sf-integral-open-scalar-unit-square`). This identifies the scalar open comparison's
  actual unit. It contains no `Operations`, `RealizationModel`, system evaluation or
  whole-system reduction mate.

Thus this delivery is a decomposition: one upper hole closed, two lower holes added, net
minus one hole closed. It does not claim a sorry-free geometric normalization. Neither lower
statement restates the original equality or assumes it under another name. The missing
pullback evaluation and the independent scalar-unit normalization are combined by real Lean
naturality and mate calculations. Zero objects, empty and identity opens, and the first
positive coefficient quotient are included in the statements and their proof plans.

## No longer needed

None. No imports, modules or nodes are withdrawn. The original statement dependencies are
retained, including the coefficient comparison module needed by `openFiniteReduction`.
The proof dependencies now name the two geometric steps and the two operation/model
interfaces used by the assembly. The unit and chapter routes are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original node's one proof step combined three separate tasks: finite evaluation of the
normalized K-flat pullback model, normalization of the scalar open mate, and the final
adjunction calculation. The existing declarations specify the relevant comparisons but do
not directly state the first two equalities. This packet makes the final calculation
explicit and exposes those two strictly intermediate tasks, with source and proof in words.
The rework record mentioned an earlier false-tail import; the current item source has no
such import, and this delivery uses no false-tail declaration.

## New nodes

`lem-sf-integral-reduction-pull-finite-square`: the normalized finite pullback square, together
with its concrete scalar comparison construction. Its sources are the original node's
K-flat evaluation argument and Stacks 07A4, 07A6, 0941 and 0D6D. This is the pullback step
before taking open mates, rather than another statement of the open-mate obligation.

`lem-sf-integral-open-scalar-unit-square`: preservation of the actual open unit by the
published scalar comparison. Its sources are the original node's coefficient-mate argument
and Stacks 03DI, 0E8I, 0D6D and 07A7. The proof plan uses restriction/pullback conjugacy,
exact localization and the normalization of the finite adjoint presentation isomorphisms.
No existing module besides the assigned item is changed and no change record is required.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
