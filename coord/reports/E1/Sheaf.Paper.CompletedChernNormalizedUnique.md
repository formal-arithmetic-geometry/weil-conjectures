## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.completedChernNormalized_unique` in
`Sheaf.Paper.CompletedChernNormalizedUnique`, preserving its complete signature and
public imports. Added proof imports of `DiagonalCompleteScalarRestriction`,
`DiagonalCompletedLineCompleteAux` and `DiagonalCompletedChernLift`; the last two use
`import all` to reuse their already proved private categorical lemmas.

Four proved private helpers establish completeness of the actual unit and root-limit
line without additional geometric hypotheses. The difference operator on a countable
power is invertible on each finite root sheaf, since that sheaf is killed by the
corresponding power of l. It stays invertible on their inverse limit. The same existing
calculation applies to the completed coefficient unit. Exact countable products in the
pro-etale constant-coefficient module category let the degree-zero embedding preserve
this operator; its invertibility implies orthogonality to l-invertible complexes.
Shift and derived direct image preserve that orthogonality by adjunction. Cancellation
of the presentation source comparison, followed by full faithfulness of completed scalar
restriction on these two complete objects, proves the equality.

The argument also covers empty schemes and schemes where l is not invertible. It uses
no local trivialization or finite-level detection of arbitrary derived morphisms.
Updated the item's DAG proof, proof dependencies and proof origin to match this argument,
and corrected the theorem's blueprint tag to its own node.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.ProEtale.RationalP1.completedChernNormalized_unique`
(node `lem-sfb-rational-p1-completed-chern-normalized-unique`).

Added 0 holes. The delivered module has 0 remaining `sorry` statements; all four private
helpers are proved. No split-off statement or new public declaration was added.

Validation: the module compiled without warnings in 10.3 seconds through `lcompile.py`.
The delivery tool additionally compiles its declaration/axiom probe and runs preflight.

## No longer needed

No imports were removed and no module or node is withdrawn. The existing public import
is needed by the unchanged statement. The proof does not invoke
`diagonalTrace_completedChern_lift`, `diagonalTrace_completedHom_bijective`,
`diagonalCompletedLine_complete` or `pur_twist_sheaf_locally_free`; in particular it does
not require their Noetherianity or invertibility hypotheses. Their modules remain in
existing dependency closures, so this delivery claims no module pruning.

The unit statement and both steps of `sk-prop-p1-adjunction-rational` are preserved.

## Where the brief, the DAG or earlier work was wrong

The original proof plan correctly required faithfulness after cancellation, but the
existing specialized completed-Hom and Chern-lift theorems require hypotheses absent from
this theorem. The completed objects can instead be shown complete directly from their
actual inverse limits, using the proved difference-operator lemmas. This closes the
obligation without strengthening its assumptions or adding another hole.

The previous docstring's blueprint tag named the parent Chern base-change node rather
than this uniqueness node; the tag now matches the declaration's DAG attachment.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CompletedChernNormalizedUnique": "5fe0ad5979586a46eaa39c0e0d1c61bbbaf3ac55"}, "results": {"Sheaf.Paper.RationalP1ScalarChernBaseChangeChernNone": {"hash": "9ffe1f004aa401e3aa9d5a1c5f6b6d65addd9e51", "status": "OK"}}, "seconds": 97, "time": "2026-10-28T10:21:10+0800", "transitive": 0, "version": 1}
```

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
