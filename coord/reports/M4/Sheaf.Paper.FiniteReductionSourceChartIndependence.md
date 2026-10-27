## What changed

Replaced the proof of
`WeilConjectures.PurityFiniteSetting.finiteReductionSourceChart_independent` without changing
its statement, definitions, or public imports. Choose `c` with `ζ = ζ' ^ c` using Mathlib's
`IsPrimitiveRoot.eq_pow_of_pow_eq_one`. Compatibility of the reduced roots gives
`η = η' ^ c`. The explicit chart power formula makes the two chart changes the same
natural-number multiple `c ^ d`. Additivity of finite reduction follows from its existing
adjunction. Postcomposition with the new reduced chart and preadditive scalar identities
then prove the required equality for the arbitrary fixed isomorphism `a`.

Added two supporting modules: `Sheaf.Paper.FiniteRootLinePowerTransition`, for the ordinary
coefficient-root chart calculation, and `Sheaf.Paper.FiniteSourceChartPowerTransition`,
for the ordered tensor induction and its transport to the intrinsic source chart.
The parent and the source-chart module use private proof imports. No existing consumer
needs adaptation. The change record is
`coord/changes/M4-finite-source-chart-power-transition.md`.

## Proved and sorry left

Closed 1 original hole and added 0 holes. Proved `WeilConjectures.PurityFiniteSetting.finiteReductionSourceChart_independent`
(node `lem-pur-finite-reduction-source-chart-independence`).

Supporting declarations are
`WeilConjectures.PurityFiniteSetting.finiteReductionRootTrivialization_inv_power`
(node `lem-pur-finite-root-line-power-transition`) and
`WeilConjectures.PurityFiniteSetting.finiteReductionSourceTrivialization_power`
(node `lem-pur-finite-source-chart-power-transition`).

All three modules compiled successfully through `lcompile.py --all` with no warnings.
The submitted sources contain zero `sorry` tokens; none remain in any delivered declaration.
The delivery tool performs the independent axiom probe and preflight checks.

## No longer needed

No existing import, module, or dependency node is pruned. The original root-chart dependency
remains necessary. The existing one-level theorem
`exists_finiteReductionSourceChartScalar` was inspected but is not imported: its unspecified
scalar does not identify the scalars at two coefficient levels. The explicit power formula
supplies precisely that information. No declaration from the adopted source tree is removed.
The unit's finite-reduction route and its realized nodes are preserved.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged. The node's scalar-cancellation plan was correct, but it hid the
ordinary root-line calculation and its transport through ordered tensor powers. These are now
separate named steps with nodes and complete proofs in words. It is unnecessary to choose an
inverse integer scalar: writing the old root as a power of the new root gives the direct scalar,
and postcomposing with an isomorphism cancels the inverse chart categorically.

Edge cases: at degree zero the tensor recursion gives scalar `c ^ 0 = 1`. The section and
categorical arguments do not require a nonempty scheme or a nonzero object. They impose no
boundedness, flatness, geometric finiteness, or finite-Tor condition on the input.

## New nodes

`lem-pur-finite-root-line-power-transition` states the ordinary inverse coefficient-root chart
power equation. It is confined to etale module sheaves, before derived functors or tensor powers.
Its proof uses the kernel inclusion into Gm, evaluation of the sheafified primitive-root map,
the existing constant-section normalization, and cancellation of the ordinary isomorphisms.

`lem-pur-finite-source-chart-power-transition` transports that equation through the actual
ordered tensor recursion. A proved private generic induction supplies the factor `c ^ d`;
exact comparison, the fixed tensor factors, and intrinsic realization transport it to the
source chart. Both nodes expand Step 2 of finite reduction in the current blueprint.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
