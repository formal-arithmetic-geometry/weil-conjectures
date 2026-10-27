# first_section_tensor_evaluation_core setting dependencies

## Reason

The core node refers to the setting of its parent theorem. This is a reference to
its definitions, not a use of the parent theorem. Recording the parent itself as
a statement dependency would create a cycle when the terminal theorem correctly
records its use of the already existing core lemma. Replace that reference edge
by the definitions which actually specify the common setting. Every Lean signature,
definition and public import stays identical.

## Old

Node `lem-sfb-rational-p1-section-evaluation-core`, `stmt_deps`:

```json
[
  "lem-sfb-rational-p1-section-evaluation",
  "def-sfb-rational-tate-pullback-comparison"
]
```

## New

The node's statement and its attached Lean signature are unchanged. Its
`stmt_deps` are the common setting definitions:

```json
[
  "def-sfb-projective-ambient-unit-counit-composites",
  "def-sfb-internal-diagonal-tensor-comparison",
  "def-sfb-projective-diagonal-composition",
  "def-sfb-projective-diagonal-pullback",
  "def-sfb-diagonal-coefficient-category",
  "def-weil-pbc-ambient-ringed-exchange",
  "sk-def-sfb-condensed-ring",
  "def-sfb-rational-tate-pullback-comparison"
]
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.RationalP1SectionEvaluation | H2 | Records the actual core dependency without a DAG cycle; no interface change. |

The node has no other current DAG citer. No downstream Lean source needs adapting.

## Status

landed 20261027T233959-L-4152567 2026-10-27 (merge of deliver/H2/Sheaf.Paper.RationalP1SectionEvaluation)
