## What changed

Replaced the body of `WeilConjectures.CompactificationCompletedRealization.completedRealization` by a proof assembling two independent sourced subresults. The original theorem signature is byte-identical. It obtains transitions from the recorded tower, the canonical specification from its unique-existence theorem, and ordered reduction from `comparison_factorization`. For constructible inputs it inverts the actual tensor-completion comparison, constructs the unique projection extension, proves the strict reduction formula by functoriality and cancellation, and proves the final realization square by tensor cancellation and adjunction-unit naturality.

Moved the thirteen existing helper constructions verbatim to `Sheaf.Paper.CompactificationCompletedRealizationData`, publicly re-exported by the original module. This permits the two proof lemmas to use their data without an import cycle. The two existing DAG attachments are updated. No helper definition, target statement, coefficient category, compact-support choice or normalization changes.

Validation: the main module compiled successfully through `lcompile.py` (21.9 seconds), as did the current finite-model statement. After independently proving image constructibility and removing it from the strict subresult, the refined main module compiled again (58.2 seconds); the strict statement compiled in 4.7 seconds. That queued strict snapshot reported a long docstring line; after wrapping it without changing Lean terms, the current strict module compiled warning-free in 3.3 seconds. The data and strict-statement modules also compiled in an import-ordered set. A byte-for-byte comparison confirms the original theorem signature and all thirteen helper declarations. All three direct consumers compiled against the changed module: `CompactifiedTowerComparisons` (59.4 seconds), `ConcreteProjectionFieldDescent` (56.1 seconds), and `CompactifiedProperTowerExchange` (52.9 seconds). They require no source changes; their byte-identical test copies were removed from the packet. The first delivery attempt exited with code 75 because all six delivery slots were occupied; it did not reach compilation or preflight. A later attempt also exited with the same slot-capacity status. The verified packet is being retried when capacity permits.

## Proved and sorry left

Closed the original hole in `WeilConjectures.CompactificationCompletedRealization.completedRealization` (node `lem-fix-compactification-completed-realization`). The main proof has zero `sorry`; the extracted data module has zero. Added two genuine subresults, each with one named theorem hole:

- `WeilConjectures.CompactificationCompletedRealization.strictRealization`, in `Sheaf.Paper.CompactificationStrictRealization`, node `lem-fix-compactification-strict-realization`: proper/open strict reconstruction and open-image constructibility, with prescribed finite projections. It contains no projection-formula assertion.
- `WeilConjectures.CompactificationCompletedRealization.finiteProjectionModels`, in `Sheaf.Paper.CompactificationFiniteProjectionModels`, node `lem-fix-compactification-finite-projection-models`: normalized models and finite scalar compatibility of the ordinary counit projection. It contains no strict-tower or completed projection-extension assertion.

Thus this is a decomposition of one original hole into two strictly smaller independent results, not a claim of a net hole reduction. Each remaining theorem has its source and full natural-language proof in its docstring and matching DAG node. The combination proof is actual Lean. Image constructibility is proved directly by transporting the property of the recorded compact-support value along the canonical qcqs realization; it is not part of the new strict theorem hole. A standalone test of this transport compiled in 2.6 seconds. In particular it does not merely apply a renamed version of the original theorem.

## No longer needed

Removed these unused private proof imports from the item module:

- `Sheaf.Paper.SfDerivedDirectImage`.
- `Sheaf.Paper.CompletedProjectionCoherence`.
- `Sheaf.Paper.CompletedCoefficientPushforwardComparison`.
- `Sheaf.Paper.IntegralTensorReductionTowerComparison`.
- `Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit`.
- `Sheaf.CategoryTheory.ReflectorAdjunctionUnitFormulas`.
- `Sheaf.SixFunctors.CompactSupportProperImageTower`.
- `Sheaf.Paper.SfIntegralDirectImageConstructible`.
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`.
- `Sheaf.Paper.OpenFiniteConstructibilityInterval`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.Paper.WeilCompletedTensorReflector`.
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`.
- `Sheaf.Paper.PerfectProjectionFormula`.
- `Sheaf.Paper.CompletedDirectImageLimits`.

The first three parent proof steps remain the proof plan of strictRealization. Finite projection compatibility remains the other subresult. Consequently these modules are removed as direct imports, not claimed globally dispensable: their mathematical work is still retained where the two new nodes cite it. No existing library module is withdrawn and no unit-level step is bypassed. The original public imports remain available through the exact data extraction. `CompletedProjectionCoherence` is not needed to derive the last square once the normalized strict map and finite identities are supplied: the square is formal naturality. The original reflector-extension and counit-restriction imports are also unnecessary for this final assembly; tensor-completion invertibility and cancellation suffice. No declaration under `WeilConjectures` is removed or altered.

## Where the brief, the DAG or earlier work was wrong

The existing Lean review already observed that the transition, canonical specification and ordered-reduction clauses restate dependency facts, while the strict projection formula and final square follow formally. The written proof now makes these reductions explicit. The difficult content left is exactly the proper/open strict comparison and finite coefficient counit identity. An existing integral-expression realization theorem was considered for model existence but rejected because its mathematical DAG has a dependency path through this item; it is not imported or used. Field-extension coefficient comparison does not cover the quotient scalar extension needed here. Evaluated isomorphisms alone do not give equality of arbitrary derived strict-system maps, so no such faithfulness argument is used.

Tool use for route review: `def-sf-projection-tensor-coefficient-comparison` (unit `sk-rem-sf-pf-done`) supplies its existing `completion_isIso` theorem on the actual normalized chi. It is used only to cancel the source completion unit on two constructible inputs. The current unit does not separately state that normalized constructible-pair lemma. `lem-weil-integral-constructible-triangulated` supplies the proved closure under isomorphisms for transport along the already canonical realization. The existing `tool_uses` approval list is left unchanged for the maintainer to review.

The finite scalar statement does not need a base-field parameter: its remaining inputs are the compactification and coefficient models. Edge checks for the subresults include zero inputs, empty schemes, the identity compactification, and index zero (the positive exponent one); no completion unit on an arbitrary incomplete tensor is inverted. In the assembly the inverted unit is only at the constructible proper/open image of K and constructible L, using the existing completion-isomorphism theorem.

## New nodes

`lem-fix-compactification-completed-realization-data` records the unchanged helper interface and its exact public re-export. The definition extraction is recorded in `coord/changes/C8-compactification-realization-data-extraction.md`, with every downstream consumer and current holder.

`lem-fix-compactification-strict-realization` records the original proper/open argument before tensor projection, with its Mathlib search evidence and exact Lean attachment.

`lem-fix-compactification-finite-projection-models` records the finite scalar counit compatibility part, with its Mathlib search evidence and exact Lean attachment.

Preflight repair: the first admitted preflight passed compilation and axiom probes, then found one metadata mismatch: the new data node recorded a definition body in `lean.statement`. This is now the exact signature, with the extraction recorded as a delivered new module. The Users table was refreshed from eight to all 24 current downstream modules, including the newly landed `AdicExceptionalCompositorCoefficientsData`; no consumer adaptation is needed.

Source verification: read the current blueprint proof in full, Stacks `lemma-Rf-commutes-with-Rlim` (including its warning that Rlim is not an ordinary derived-category limit), `equation-projection-formula-map`, `lemma-projection-formula`, and `remark-compatible-with-diagram`. The finite scalar assertion uses the compatibility of actual maps, rather than any assertion that the finite projection is invertible.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
