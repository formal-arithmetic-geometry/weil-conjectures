## What changed

Replaced the proof hole of
`AlgebraicGeometry.Scheme.PurityIntegralTower.normalizedTateTensorTower_core`
by an assembly from three strictly smaller steps. The theorem statement, public
import, coefficient objects, and every definition remain unchanged.

The proof obtains a derived lift of the strict ordinary quotient tower and
ordinary projection-balanced quotient isomorphisms. It constructs the finite-level
isomorphisms as the quotient-level identification, the single of inverse ordinary
balancing, and inverse `finiteModelIso`. Cancellation and naturality of the exact
restriction/single comparison prove `ProjectionNormalized`; this computation is
written in the item, not postponed to a new theorem. The existing proved
`quotientRootLineComparison` supplies the finite comparison existence clause at
exponents `b+1` and `a+1`. The remaining single-pair square is applied to this tower.

Added proof imports of `QuotientRootLineComparison`, `TateTensorQuotientBalancing`,
`StrictTateTensorTowerLift`, and `TateTensorNormalizedSquare`. New modules use the
existing data module publicly because their statements use its objects.

Validation: all three new modules compiled individually in import order (26.7,
6.3, and 6.6 seconds). The completed assembly compiled against their artifacts
in 16.2 seconds. A textual check confirms the original theorem signature is
identical, all Lean lines meet the 100-character limit, and each node's
`proof_deps` is the union of its proof-step dependencies.

## Proved and sorry left

One original hole is closed, by name:
`AlgebraicGeometry.Scheme.PurityIntegralTower.normalizedTateTensorTower_core`
(node `lem-pur-normalized-tate-tensor-reductions`). This is a decomposition, not a
sorry-free proof of the mathematical construction. The finite comparison existence
clause and the assembly of `ProjectionNormalized` are proved in the item.

Three holes are added, one public named theorem per new module:

- `AlgebraicGeometry.Scheme.PurityIntegralTower.tateTensorQuotient_balancing`
  (`lem-pur-tate-tensor-quotient-balancing`): ordinary sheaf balancing at a single
  level, with its generator formula; no derived tower or scalar square.
- `AlgebraicGeometry.Scheme.PurityIntegralTower.strictTateTensorTower_lift`
  (`lem-pur-strict-tate-tensor-tower-lift`): quotient-linear derived levels of the
  strict ordinary tower, with their exact evaluation equation; no finite root
  identifications, finite comparisons, or scalar square.
- `AlgebraicGeometry.Scheme.PurityIntegralTower.tateTensor_normalizedSquare`
  (`lem-pur-tate-tensor-normalized-square`): one comparison square for an existing
  projection-normalized tower and a supplied comparison; no existence assertion.

The item's actual remaining hole count is zero; the delivery contains three holes.
Holes closed: 1. Holes added: 3. Net: -2. No hole occurs in a definition, private
helper, or partial proof. Each remaining theorem has a source, a full proof in
words, and a matching node. Empty schemes, zero tensor powers, and equal reduction
indices were checked in the mathematical arguments; none of the statements
requires nonemptiness, positive tensor degree, or strict inequalities.

## No longer needed

No existing import, module, or node is globally pruned. The parent now directly
uses the three new component nodes and the existing quotient-root-line comparison.
Its former proof dependencies remain below the component nodes; their mathematics
is still needed. The unit's adic reconstruction route is unchanged.

Mathlib search found tensor/direct-limit and roots-of-unity algebra, but no theorem
with the actual sheaf projections and strict tower normalization. General ordinary
line/scalar comparison theory does not by itself identify these projections or
supply this strict ordinary quotient tower. The existing quotient-root-line
comparison is reused instead of restating its existence as another hole.

## Where the brief, the DAG or earlier work was wrong

The current server queue lists this item as a proof task with one hole. Its older
rework entry records quarantine after the 2026-10-27 global build, whose error was
bad import `Sheaf.Paper.CondensedTateIntegralTowerData`. The item and that dependency
are present in the current snapshot, and the original item compiled against the
published build before editing. This delivery preserves the restored attachment
and all objects; it does not withdraw the item or replace it with an empty module.

The delivery overlay compiles the restored attachment and its proof imports against
the current published artifacts. No existing module is adapted.

The original plan treated the ordinary balancing, K-flat derived lift, and finite
comparison square as prose in one hole. These are now independently stated Lean
obligations. No target or definition is weakened. No claim is made that the three
new obligations have been proved.

## New nodes

`lem-pur-tate-tensor-quotient-balancing` isolates proof Step 1 of the assigned node.
It is a fixed-level assertion about ordinary sheaves, with exactly
`ProjectionBalanced`, before localization. Module: `TateTensorQuotientBalancing`.

`lem-pur-strict-tate-tensor-tower-lift` isolates Steps 2--3 through construction of
quotient-derived levels. Its equation fixes evaluation before any finite model is
chosen. Module: `StrictTateTensorTowerLift`.

`lem-pur-tate-tensor-normalized-square` isolates Step 4 after the tower has been
constructed. It takes an existing tower, its projection normalization, one
comparable pair, and one finite comparison. Module: `TateTensorNormalizedSquare`.

All inherit chapter `sec-smooth-purity` and unit `sk-thm-purity-transport` and cite the
current blueprint's adic-stage step and the assigned node's detailed argument.
LeanSearch, LeanFinder, Loogle, Mathlib/project grep, and blueprint title searches
are recorded in the nodes. There are no interface changes to existing declarations.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.NormalizedTateTensorTowerCore": "c9f24b8719d66395933946e611d53252b4b962db", "Sheaf.Paper.StrictTateTensorTowerLift": "16a530c1d76eea0ec643c00028203d13146930b9", "Sheaf.Paper.TateTensorNormalizedSquare": "5aa9032b0848bb7eddc9cd12194f97a0868af943", "Sheaf.Paper.TateTensorQuotientBalancing": "f06b6bf6e61c61a3604ee27571bb542f6bf19164"}, "results": {}, "time": "2026-10-28T00:47:50+0800", "transitive": 0, "version": 1}
```

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
