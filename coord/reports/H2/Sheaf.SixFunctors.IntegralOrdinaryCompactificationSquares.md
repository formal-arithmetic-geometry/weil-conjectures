## What changed

Replaced the original hole in
`WeilConjectures.IntegralSystemRealization.ordinaryCompactificationSquares`
by a conjunction proof, preserving its signature. Its projection clause is completely
proved: specialize the existing proper-projection square to formal variables, insert
both child coefficients by naturality, invert the open-projection coefficient square,
transport the inverse pull compositor along the actual `cf.comm` equation, and paste
these three squares after proper image.

The exchange clause is isolated in the new module
`Sheaf.SixFunctors.IntegralOrdinaryCompactificationExchangeSquare`. It retains proved
private helpers for the generic mate-pasting square, the actual pullback coefficient
boundary, the native specialization to proper exchange, and forward open base change.
The last helper uses the inverse-open mate unit equation and inverse cancellation,
without imposing quasi-compactness on the compactification open.

All new proof imports are private. No other existing Lean module, public definition,
instance or attribute is changed. The parent node and new exchange node record this
route. The projection argument is substantive; this delivery is a partial decomposition,
not a claim that both compactification squares are now proved.

## Proved and sorry left

Original hole closed:
`WeilConjectures.IntegralSystemRealization.ordinaryCompactificationSquares`
(node `lem-sf-integral-ordinary-compactification-squares`). Its projection clause and all
private helpers in both delivered modules are proved.

One hole added and left:
`WeilConjectures.IntegralSystemRealization.ordinaryCompactificationExchangeSquare`
(node `lem-sf-integral-ordinary-compactification-exchange-square`). It is exactly the
exchange clause alone, without any tensor/projection conclusion. It has a complete
proof in words and checked private ingredients. Thus the original module has zero
holes, the new module has one, and the packet closes one upper hole while adding one
strictly smaller lower hole. This is a decomposition, not a net hole reduction.

The projection proof uses `ordinaryExchangeProjectionSquares.2`; obligations in that
existing dependency are not duplicated here.

## No longer needed

No existing module or node is withdrawn. The original four dependency modules are still
used by projection and/or the exchange helpers. The new exchange module does not import
`IntegralOrdinaryExchangeProjectionSquares`: its proper-exchange helper follows directly
from the pullback boundary and generic mate calculus. The parent retains that dependency
for proper projection. No intermediate obligation for projection is introduced.

LeanFinder and Loogle found generic mate calculus rather than the project coefficient
maps. Local searches found the existing private open mate and inverse compositor helpers,
which are reused through private `import all` imports.

## Where the brief, the DAG or earlier work was wrong

The historical build-error file reports a missing
`IntegralOrdinaryExpressionReduction`. Current server records assign this as a one-hole
proof item and the dependency source exists. No import repair or withdrawal is needed.

The exchange draft closes its tactic goals but fails kernel checking with a deterministic
timeout. The slow point is converting evaluated mate components between the scalar-source
and raw ringed-module category instances. The same issue occurs in the explicit proper
exchange helper and even the objectwise compactification-exchange decomposition. A native
specialization whose type is inferred with `type_of%` checks quickly. Explicit functor and
category arguments, equation-based folding/unfolding, transposition directly in the concrete
goal, normalization to unit/counit components, local instance priorities, and congruence
conversion did not fix the concrete kernel conversion. No time limit was raised and no
transparency-respect option was disabled. Failed diagnostics remain outside `lean/` in the
sandbox scratchpad and are not part of the delivery.

The remaining exchange statement is strictly smaller than the original conjunction:
projection is now proved, not moved to another hole. Its docstring gives the actual
pasting argument and describes this remaining implementation problem.

## New nodes

`lem-sf-integral-ordinary-compactification-exchange-square`, realized by
`Sheaf.SixFunctors.IntegralOrdinaryCompactificationExchangeSquare`, carries only the
exchange clause of the original item. It keeps the same hypotheses and prescribed maps
for that clause, and adds no assumptions. Its private mate and open-square ingredients
are proved. No change record is necessary: existing signatures and definitions are
unchanged and only the item's node and a new node are edited.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralOrdinaryCompactificationExchangeSquare": "ec5317437eef0bea692e79e2871f913b5d660279", "Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares": "8b89f269177bdb75db7085017ff39c046c316186"}, "results": {"Sheaf.SixFunctors.IntegralBasicGeneratorSquare": {"hash": "4688416ee2b87e73009b2dee904c25a31425339a", "status": "OK"}}, "seconds": 37, "time": "2026-10-28T03:48:34+0800", "transitive": 0, "version": 1}
```

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
