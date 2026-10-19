## What changed

Retained the earlier attempt and compared it against the current module and its node.
The item has a proof of the generic abelian exchange by a limit of affine generic
neighbourhoods, coefficient forgetting and reflection of isomorphisms, field-extension
exchange, comparison with the chosen iterated pullbacks, and module mate pasting.
All added helpers are private and proved; public statements
and definitions remain unchanged. The three added imports are proof-only: connected
limits in over categories, additive geometric stalks, and inverse-image coherence.

The module compiles cleanly through `lcompile.py` (10.9 seconds). The complete
`deliver3.py --no-push` compile, axiom probe and server preflight passed. Explicit
projection equations and an explicit unbounded stalk type avoid expensive conversion
of nested cone and derived-category definitions. The unused-tactic linter is disabled
only on the private generic-limit helper, where the explicit type annotation is retained
for elaboration performance. No new axioms or declarations with sorry are introduced.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.genericDirectImageExchange`
(node `lem-sf-etale-generic-direct-image-exchange`). Holes closed: 1 of 1;
holes added: 0; holes remaining in the delivered module: 0; split off: 0.
The original statement is unchanged, and both its invertibility and canonical
pasting-equality clauses are proved from the declared dependencies.
The proof intentionally uses the declared SmoothBaseChangeLimit,
FieldExtensionExchange, UnboundedExchangeAgrees, UnboundedAbelianExchangeComparison,
and ModuleExchangeCompositeBaseChange interfaces. Their pre-existing obligations
remain with their modules and are not new holes in this delivery.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.LimitFibreProducts` and the
proof dependency and tool-use entry `lem-weil-pbc-limit-fibre-products`. Mathlib's
`Over.isLimitLiftCone`, preservation of limits by the right adjoint `Over.pullback`,
and preservation of connected limits by `Over.forget` give the specified limit cone
directly. No unit step is bypassed. The unit has no realized nodes in its record.

Removed `Mathlib.AlgebraicGeometry.Morphisms.Proper`: no properness result is used;
the smooth base-change instance is supplied by the existing Smooth import. The node
`lem-pc-proper-base-change` is retained for its smoothness clause. No other stated
proof dependency is pruned. No public import is removed.

## Where the brief, the DAG or earlier work was wrong

The retained sandbox had no report and its proof did not compile. The initial dry run
reported the missing report. Search records retained from the earlier attempt include
LeanFinder, Loogle and grep, none supplying the complete exchange theorem. Reading
the current source library shows its generic open-immersion exchange has a different
scope; the declared 0F09/0F1C route is appropriate. Checked the source text of Stacks
0F09 and 0F1C and the current dependency signatures. The zero coefficient ring,
N=1, zero object, empty source and inseparable field-extension cases require no added
hypotheses. No definition or statement repair, new node or forced adaptation is made.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
