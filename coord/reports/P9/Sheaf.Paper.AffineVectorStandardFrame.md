## What changed

Filled `WeilConjectures.PurityFiniteSetting.affineVectorStandardFrame` without changing
its statement or any existing definition. Proved private helpers for ordered coefficient
squares, exchange composition, affine compact-trace base change, and the frame normalization.
The final proof evaluates the existing normalization on the top open, transports it along
`B.topIso.inv`, and identifies the constant target with the monoidal unit. Updated the item's
DAG proof to record precisely these existing dependencies. No other existing module changes.

## Proved and sorry left

Closed 1 of 1 holes: `WeilConjectures.PurityFiniteSetting.affineVectorStandardFrame`
(node `lem-pur-affine-vector-standard-frame`). Added 0 holes; 0 remain in the item.
All private helpers are proved. This is a proof from existing declarations, with no new
split-off statement. Compilation and delivery validation are recorded by the delivery tool.

## No longer needed

No original public imports were removed; no modules are withdrawn or pruned.
The old direct DAG dependency `lem-amb-affine-space-top-trace` is replaced by the specific
already-proved tower counit base-change equation; the top-trace construction still occurs
transitively in vector integration. The old direct dependency
`lem-kun-derived-pullback-composition-monoidal` is replaced by the more specific existing
constant-unit composition and constant-to-monoidal-unit comparison equations. No generic
tensor-composition theorem or faithful-pullback cancellation is needed in this proof.

## Where the brief, the DAG or earlier work was wrong

The proof plan was mathematically sufficient. Its coefficient-recursion and unit gluing
steps already have proved APIs: `affineTraceRightBaseChange_unit_coefficient`,
`orderedTateCoefficientComposition`, `ordinaryFiniteUnitPullback_comp`, and
`SfP1Transport.constantUnit_pullback`. These avoid another split. The same equations cover
rank zero, the empty base, and zero coefficients; no additional hypotheses are introduced.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
