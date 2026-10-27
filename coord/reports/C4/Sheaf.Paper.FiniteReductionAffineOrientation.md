## What changed

Proved `existsUnique_finiteReductionOrientationExceptionalComparison` from the
constructible exceptional adjunction and the already specified compact-support
coefficient mate. Its statement and the exceptional comparison definition are unchanged.
Added the fully proved `finiteReductionLineInput_constructible` in
`Sheaf.Paper.FiniteReductionLineInputConstructible`: primitive-root charts identify the
shifted line with the shifted coefficient unit; a degree-zero rank-one flat model
supplies its finite-Tor constructibility. A private helper transports general finite
exceptional preservation to `compositionExceptional` through right-adjoint uniqueness.
Proof imports expose the existing private counit bijection and the general finite
exceptional preservation interface. No target or existing public signature changes.

## Proved and sorry left

Closed one of the item's two original holes:
`WeilConjectures.PurityFiniteSetting.existsUnique_finiteReductionOrientationExceptionalComparison`.
The new public theorem
`WeilConjectures.PurityFiniteSetting.finiteReductionLineInput_constructible` and all
private helpers are proved. Added holes: zero. Split-off holes: zero.

One original hole remains:
`WeilConjectures.PurityFiniteSetting.finiteReductionOrientationExceptionalComparison_isIso`
(node `def-pur-finite-affine-orientation-comparison`). Its statement and source proof
remain unchanged. The existence proof is a proof from existing declared dependencies,
not a relocation of its hole.

## No longer needed

No existing nodes or modules are withdrawn. No prior proof dependency is pruned:
the geometry, supported Kummer class, root charts and input-comparison dependencies
are still used by the other declarations of this module. No new orientation or smooth
purity theorem is required to construct the exceptional coefficient arrow.

## Where the brief, the DAG or earlier work was wrong

The general exceptional comparison in `FiniteReductionComparisons` assumes smoothness,
so it does not specialize to a closed zero section. Its proved private counit bijection
has no smoothness hypothesis and applies here. Finite exceptional preservation applies
to arbitrary separated finite-type maps. The fixed exceptional functor and the chosen
ordinary etale right adjoint are related by the same right-adjoint uniqueness construction as `fixedExceptionalIso`, rather
than assumed definitionally identical.

The generic tools `lem-coef-finite-exceptional` (preservation and adjoint uniqueness),
`lem-weil-finite-ctf-triangulated`, `lem-pur-finite-locally-free-line-models`,
`lem-pur-constructible-single-support`, and
`lem-weil-pbc-independent-sheaf-tensor-colimits` are used only for these interfaces.
The unit's finite-reduction and twist route is preserved. Any needed cross-unit tool
approval is left to the maintainer; no `tool_uses` field is added by this delivery.

## New nodes

`lem-pur-finite-reduction-line-input-constructible` attaches the completely proved
shifted-root-line constructibility theorem. It is strictly a domain condition for the
adjunction argument, introduces no new hole, and allows arbitrary k-schemes and every
positive coefficient level. Its primitive-root chart and flat-model argument also cover
the empty scheme and level one. Mathlib and blueprint searches found no exact duplicate.
No change record is needed: existing statements, definitions and public imports retain
their meaning.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
