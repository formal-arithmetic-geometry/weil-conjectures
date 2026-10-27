## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.lisseTower_localized_realization`
with a complete Lean proof assembling the actual-level and constant-model comparisons
using one fixed scalar comparison. Its signature, the existing realization definition,
and all five fields of `LisseTowerLocalizedComparisons` stay unchanged.

Added `Sheaf.Paper.LisseTowerPulledScalar`, with a constructed natural scalar
isomorphism. `lisseTowerNormalizedScalarSquare` selects the unique square supplied by
the existing scalar-restriction theorem; its section property is proved.
`lisseTowerFixedScalarIso` localizes that square with the fixed realization's exact
composition comparisons. `lisseTowerPulledScalarIso` pastes it with the existing
inverse-image coefficient mate and the actual finite-to-completion restriction
compositor. No data are chosen from an arbitrary existence theorem, and this module
has no proof holes of its own.

Added two separate proof obligations. `Sheaf.Paper.LisseTowerLocalizedActual` concerns
only transport of the supplied actual levels and their descent equation at one local
triple. `Sheaf.Paper.LisseTowerLocalizedConstants` concerns only constant algebraic
complexes and their semilinear arrows. The latter is independent of M, D, delta,
e, c and the descent equation; its scheme maps need no common factorization.
Neither theorem asserts the other branch or the full localized-comparisons record.
Both use the same explicitly constructed scalar, so their witnesses combine without
any further compatibility assumption. Each remaining theorem has a source and a
complete proof in words in its docstring and node.

The four modules compiled together in import order. The initial complete set took
5.1, 7.3, 8.0 and 19.2 seconds per file. The constant theorem was then simplified to
arbitrary scheme maps, and its caller was rechecked. All files remain below the
60-second limit. Delivery runs the mandatory compiler and axiom probes.

## Proved and sorry left

Closed the original hole by declaration name:

- `AlgebraicGeometry.Scheme.lisseTower_localized_realization`
  (`lem-weil-pbc-lisse-tower-localized-realization`).

Added two named holes:

- `AlgebraicGeometry.Scheme.lisseTower_localized_actual`
  (`lem-weil-pbc-lisse-tower-localized-actual`).
- `AlgebraicGeometry.Scheme.lisseTower_localized_constants`
  (`lem-weil-pbc-lisse-tower-localized-constants`).

The item has zero remaining holes; the delivery adds two. This is a decomposition:
one hole closed, two added, net minus one before any later proof work. It is not a
sorry-free proof of the original assertion. The new scalar construction has zero
holes and proves `lisseTowerNormalizedScalarSquare_sections` from the existing
`lisseTower_scalar_restriction`; that existing dependency is still unproved.

## No longer needed

None. No existing import or module is pruned. The original public scalar-restriction
import remains necessary for the item's statements. The original node's direct
proof dependencies are replaced by the constructed scalar and the two smaller
obligations. Its earlier dependencies remain needed in the two subsidiary arguments;
this is a reorganization of those dependencies, not a claim of pruning them.

## Where the brief, the DAG or earlier work was wrong

No false statement or error in the unit route was established. The original node's
three prose steps do not by themselves provide Lean declarations for the ordinary
fixed-realization/inverse-image comparison or the two exact normalized equations.
Mathlib provides ordinary sheafification/pullback, constant-sheaf, and scalar APIs,
and the project provides the coefficient mates, but these do not directly state
those comparisons for the concrete coefficient presentations.

The construction of the scalar field can be closed immediately from those existing
APIs and need not travel through another existence obligation. The remaining work
is separated into actual descent and algebraic constants, rather than renaming the
whole record. The constant branch has no descent assumptions at all. Zero objects,
zero coefficient rings and empty bases cause no exception: the comparisons and
ordinary section identities used in their proof plans still apply. There is no
boundedness or finite Tor-amplitude premise added. The blueprint unit and target
statements are unchanged. No source-library file or other existing module is edited.

## New nodes

`lem-weil-pbc-lisse-tower-pulled-scalar`, module
`Sheaf.Paper.LisseTowerPulledScalar`, records the constructed localized scalar square
and its proved section-normalization theorem. Its main remaining dependency is the
existing normalized ordinary square theorem.

`lem-weil-pbc-lisse-tower-localized-actual`, module
`Sheaf.Paper.LisseTowerLocalizedActual`, records the actual-level part of original
steps 1 and 2, retaining the exact specified scalar and actual restricted transition.

`lem-weil-pbc-lisse-tower-localized-constants`, module
`Sheaf.Paper.LisseTowerLocalizedConstants`, records the constant-complex part of step 1
and the arbitrary algebraic-arrow equation of step 3. It needs no actual tower or
supplied descent equation.

There are no change records: only the item's proof, its proof-dependency node,
and the three new modules and nodes are changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.LisseTowerLocalizedActual": "2183a3c5e83c368dda979ff64c4957487ea181e1", "Sheaf.Paper.LisseTowerLocalizedConstants": "3ff049d1303273e7f81e98bd8d741d1b221c6dae", "Sheaf.Paper.LisseTowerLocalizedRealization": "7fc02abbc15c7911b37fc7c4d346153166d44694", "Sheaf.Paper.LisseTowerPulledScalar": "5533bee635e40ba11739ae183a19f530436e3d9e"}, "results": {}, "time": "2026-10-28T06:29:46+0800", "transitive": 0, "version": 1}
```

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
