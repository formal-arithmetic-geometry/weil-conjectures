## What changed

Proved `WeilConjectures.CoefQbarVerdier.dualizing_descent` in
`Sheaf.SixFunctors.CoefQbarVerdierDualizing` without changing its statement,
public imports, or any definition. Added private proof imports of
`CoefQbarVerdierCore` and `RationalDualizingIdentification`; the existing
`CoefQbarVerdierExceptional` proof import is used.

Core descent and completion supply a base-point duality. Exceptional descent
then supplies A at the canonical structure compactification. The existing
`RationalOperations.rationalDualizing_identification` applies to this exact
A.system and each B.finite.omega E. At the base coefficient field, reverse
B.omegaComparison, map the finite isomorphism through the inclusion, and
compose with A.rightComparison at the finite coefficient unit. Its endpoints
are the unchanged statement's B.omega and A.right applied to coefficientUnit.
The finite family uses the same A.system at every field.

Updated the assigned node's proof, proof_deps and proof_origin to match this
argument. The unit's realized statement and steps lists are empty, and its
finite-to-rational-to-closed coefficient route is preserved.

Validation: lcompile.py compiled the delivered module successfully in 5.7 s,
with exit code 0 and no warnings. Import-direction checks permitted both new
private proof imports. Every Lean line is at most 100 characters.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.CoefQbarVerdier.dualizing_descent`
(node `lem-coef-qbar-verdier-dualizing-descent`).

No sorry remains in the item, and no new hole or theorem was added.
This is a proof from existing stated dependencies, not a new decomposition.
In particular core_descent, exceptional_descent and
rationalDualizing_identification remain existing downstream obligations.

## No longer needed

No existing import was removed. Each of the three private proof imports is
used, and the public data import is retained unchanged.

The assigned node no longer directly needs `lem-coef-integral-finite-extension`
(module `Sheaf.SixFunctors.CoefIntegralFiniteExtension`) or the full
`lem-coef-rational-operations` conclusion (module
`Sheaf.SixFunctors.RationalOperations`). Its proof uses the already stated
`lem-sf-rational-dualizing-identification` from
`Sheaf.SixFunctors.RationalDualizingIdentification` instead. These broader
modules can still be needed transitively or by other consumers; no global
withdrawal is claimed. There is no new construction of coherent finite
isomorphisms across all fields: the goal only asks for an isomorphism in the
common-stage category and separate finite identifications, so the base-stage
isomorphism and the universal finite theorem suffice.

## Where the brief, the DAG or earlier work was wrong

The planned finite-normalization uniqueness and scalar-extension descent were
unnecessary here: rationalDualizing_identification already accepts an arbitrary
normalized exceptional system and coherent finite dualizing datum. The result
therefore applies to the system returned by exceptional_descent directly,
without comparing it with a different system obtained from
coef_rational_operations. No false statement or definition repair was found.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
