## What changed

Restored `Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting` from quarantine and
repaired the kernel-checking timeout recorded at original line 167 after the
2026-10-20 upstream sync.

Expanded the public theorem's local functions `P`, `θ`, `c`, and `i`, and its
coefficient alias `A`. The coefficients are written explicitly as
`AddCommGrpCat.{u + 1}` throughout. This is a definitionally equal statement: a token
comparison after explicit substitution verifies that every binder and every
one of the three equations is otherwise identical. There is no mathematical
statement change, no added hypothesis, and no weakened conclusion.

The existing private horizontal and vertical lemmas now conclude with the
source composition comparison already cancelled. Two fully proved generic
cancellation helpers use `Iso.inv_comp_eq`. A private `comparison_laws` assembles
the explicit generic formulas, and the public theorem specializes them to
abelian groups. All definitions, instances, attributes and public imports
remain unchanged. Both existing imports are needed. No consumer adaptation is
required; searches of active and quarantined Lean sources find no other user
of the theorem or importer of the module.

The DAG attachment records the expanded Lean signature, and its proof text
records the cancellation and specialization. Its mathematical statement,
proof dependencies, and unit route remain unchanged. Change record:
`coord/changes/P9-derived-square-pasting-let-expansion.md`.

## Proved and sorry left

This is a zero-hole repair. The quarantined module had 0 `sorry`, and the
delivered module has 0 `sorry`. Holes closed: none. Holes added: none.
No split-off statements. `AlgebraicGeometry.Etale.derivedSquareIsoPasting`
and every private helper have complete proofs. The public theorem realizes
`lem-weil-pbc-derived-square-iso-pasting`.

The expanded formulation compiled on the project server. Diagnostic options
and lowered heartbeat budgets used to find the expensive conversions were
removed; the delivered file uses the normal project limits. The delivery dry
run supplies the declaration-by-declaration axiom check.

## No longer needed

None. No imports, modules, nodes, or source declarations were removed.
The direct coherence route and its declared proof dependencies remain.

## Where the brief, the DAG or earlier work was wrong

The assigned module is in `quarantine/Sheaf/AlgebraicGeometry/`, rather than the
active `lean/Sheaf/AlgebraicGeometry/` tree. Its earlier proof was complete but
failed kernel checking after the upstream sync. This delivery repairs that
failure rather than claiming a new closed proof hole.

The local-function notation in the old public signature caused expensive
conversions involving derived-functor and sheaf-pullback constructions. Simply
moving final simplification into a generic helper did not repair it. Expanding
that notation and assembling the explicit formulas removed the bottleneck.
No upstream source definition or declaration was changed.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
