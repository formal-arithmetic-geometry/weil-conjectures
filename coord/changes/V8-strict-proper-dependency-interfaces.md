# V8: granular dependencies for strict proper reduction

## Reason

The existing ordinary realization results can prove the strict proper reduction map. Their broad former interface nodes also contain later compact-support, finite-expression and completion realization data. Citing those broad owners creates a DAG cycle back to the item although the Lean import graph is acyclic. The new interface nodes isolate existing concrete declarations, following the prior strict-coefficient interface split. No Lean signature, definition, attribute or public import changes in any shared module.

## Old

- `lem-sf-integral-proper-finite-projection`: stmt_deps = `def-sf-integral-system-canonical-bridge`, `def-sf-integral-system-operations`, `lem-weil-derived-scalar-extension-restriction-adjunction`, `lem-pur-compact-support-integral-coefficient-comparison`, `lem-coef-derived-system-evaluation-calculus`.
- `lem-sf-integral-reduction-pullback-model`: stmt_deps = `def-sf-integral-system-canonical-bridge`, `def-sf-integral-system-operations`.
- `lem-sf-integral-ordinary-limit-model`: stmt_deps = `def-coef-ringed-sequence-site`, `def-weil-completed-integral-coefficients`, `def-sf-integral-system-canonical-bridge`, `def-pur-completed-pullback-tensor-comparison`, `def-weil-pbc-proetale-operations`.
- `lem-sf-integral-ordinary-tower-comparison`: stmt_deps = `def-pur-completed-pullback-tensor-comparison`, `def-coef-ringed-sequence-site`, `def-weil-derived-direct-image`.
- `lem-sf-integral-completed-direct-image-comparison`: stmt_deps = `def-weil-derived-direct-image`, `def-weil-pbc-proetale-operations`, `def-pur-integral-compact-support-coefficient-data`, `def-weil-completed-integral-coefficients`.
- `lem-sf-integral-system-operation-models`: stmt_deps = `def-sf-integral-system-operations`, `def-sf-integral-system-canonical-bridge`.
- `lem-sf-integral-system-direct-evaluation`: stmt_deps = `def-sf-integral-system-operations`.
- `lem-sf-integral-system-open-comparisons`: stmt_deps = `def-sf-integral-system-operations`.
- `lem-sf-integral-system-open-evaluation`: stmt_deps = `def-sf-integral-system-operations`.
- `lem-sf-integral-direct-evaluation-mate-invertible`: stmt_deps = `def-sf-integral-system-operations`, `def-pur-completed-pullback-tensor-comparison`, `def-weil-pbc-adjunction-mate`.
- `lem-sf-integral-pull-evaluation-quotient-square`: stmt_deps = `def-sf-integral-system-operations`, `def-pur-completed-pullback-tensor-comparison`, `def-weil-pbc-adjunction-mate`.

## New

Four definition nodes attach the existing finite pullback evaluation, strict-system operation data, ordinary/K-flat realization data, and ordinary completed direct-image data. Their statements explicitly exclude the unrelated later realization interfaces. The mathematical statements of the eleven existing theorem nodes are unchanged; citation text and dependency records now point to the relevant smaller interface. Each node records the old fields and the audit of every direct citer.

- `lem-sf-integral-proper-finite-projection`: stmt_deps = `def-strict-coefficient-system-realization-data`, `def-strict-coefficient-system-operation-data`, `lem-weil-derived-scalar-extension-restriction-adjunction`, `lem-strict-coefficient-finite-geometric-coordinates`, `lem-coef-derived-system-evaluation-calculus`.
- `lem-sf-integral-reduction-pullback-model`: stmt_deps = `def-strict-coefficient-system-realization-data`, `def-strict-coefficient-system-operation-data`.
- `lem-sf-integral-ordinary-limit-model`: stmt_deps = `def-coef-ringed-sequence-site`, `def-weil-completed-integral-coefficients`, `def-strict-coefficient-system-realization-data`, `def-pur-completed-pullback-tower-core`, `def-weil-pbc-proetale-operations`.
- `lem-sf-integral-ordinary-tower-comparison`: stmt_deps = `def-pur-completed-pullback-tower-core`, `def-coef-ringed-sequence-site`, `def-strict-coefficient-completed-image-data`.
- `lem-sf-integral-completed-direct-image-comparison`: stmt_deps = `def-strict-coefficient-completed-image-data`, `def-weil-pbc-proetale-operations`, `def-strict-coefficient-ringed-geometric-data`, `def-weil-completed-integral-coefficients`.
- `lem-sf-integral-system-operation-models`: stmt_deps = `def-strict-coefficient-system-operation-data`, `def-strict-coefficient-system-realization-data`.
- `lem-sf-integral-system-direct-evaluation`: stmt_deps = `def-strict-coefficient-system-operation-data`.
- `lem-sf-integral-system-open-comparisons`: stmt_deps = `def-strict-coefficient-system-operation-data`.
- `lem-sf-integral-system-open-evaluation`: stmt_deps = `def-strict-coefficient-system-operation-data`.
- `lem-sf-integral-direct-evaluation-mate-invertible`: stmt_deps = `def-strict-coefficient-system-operation-data`, `def-strict-coefficient-pullback-evaluation-data`, `def-weil-pbc-adjunction-mate`.
- `lem-sf-integral-pull-evaluation-quotient-square`: stmt_deps = `def-strict-coefficient-system-operation-data`, `def-strict-coefficient-pullback-evaluation-data`, `def-weil-pbc-adjunction-mate`.

## Users

All Lean users retain the identical declarations and proofs. No Lean consumer needs adaptation or recompilation against a changed interface because no shared Lean file is changed. The item and its new presentation theorem compile against the existing declarations. Each direct DAG citer below remains valid for exactly the same mathematical reason; only the owner of a cited definition changes.

- `lem-sf-integral-proper-finite-projection`: `lem-sf-integral-support-projection-transport`. All hold: the Lean assertion and its proof are verbatim.
- `lem-sf-integral-reduction-pullback-model`: `lem-sf-integral-canonical-ambient-models`, `lem-sf-integral-basic-realization`. All hold: the Lean assertion and its proof are verbatim.
- `lem-sf-integral-ordinary-limit-model`: `lem-sf-ordinary-reduction-pull-composition`, `lem-sf-integral-reduction-pullback-model`. All hold: the Lean assertion and its proof are verbatim.
- `lem-sf-integral-ordinary-tower-comparison`: `lem-sf-integral-ordinary-limit-model`. All hold: the Lean assertion and its proof are verbatim.
- `lem-sf-integral-completed-direct-image-comparison`: `lem-sf-integral-ordinary-limit-model`. All hold: the Lean assertion and its proof are verbatim.
- `lem-sf-integral-system-operation-models`: `lem-sf-integral-canonical-system-coherence`. All hold: the Lean assertion and its proof are verbatim.
- `lem-sf-integral-system-direct-evaluation`: `lem-sf-integral-system-operation-models`. All hold: the Lean assertion and its proof are verbatim.
- `lem-sf-integral-system-open-comparisons`: `lem-sf-integral-system-operation-models`. All hold: the Lean assertion and its proof are verbatim.
- `lem-sf-integral-system-open-evaluation`: `lem-sf-integral-system-operation-models`. All hold: the Lean assertion and its proof are verbatim.
- `lem-sf-integral-direct-evaluation-mate-invertible`: `lem-sf-integral-system-direct-evaluation`. All hold: the Lean assertion and its proof are verbatim.
- `lem-sf-integral-pull-evaluation-quotient-square`: `lem-sf-integral-system-direct-evaluation`. All hold: the Lean assertion and its proof are verbatim.

## Status

landed 20261027T103518-L-1094397 2026-10-27 (merge of deliver/V8/Sheaf.Paper.StrictCoefficientProperReduction)
