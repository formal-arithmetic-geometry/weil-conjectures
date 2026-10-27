## What changed

Replaced the proof of
`AlgebraicGeometry.Etale.SystemProjection.etaleCofinalSupport_realization` with an
explicit construction from two smaller geometric statements. The existing signature,
docstring and public import are unchanged.

The ordinary restriction compositor is constructed using Mathlib's
`SheafOfModules.pushforwardComp` and `pushforwardCongr`. Its maps are proved to be
identity maps on selected sections. A generic private helper keeps this proof abstract
from the large sequence-ring definitions.

The support isomorphism is the composite of the X factorization, inverse coefficient
projection, derived repetition comparison, and inverse Y factorization. Functoriality
and inverse cancellation prove its normalization. The new, proved theorem
`etaleCofinalSupport_evaluation` derives its level formula from the factor and repetition
evaluation diagrams, coefficient-projection evaluation, and three naturality squares.
It does not use faithfulness of evaluation on derived categories.

The block construction chooses the geometric projection presentation together with
its section normalizations. Invertibility for this same presentation is proved by
joint reflection of isomorphisms through exact level evaluation, using the finite-level
part of `etaleSystemCoefficientProjection`. Coefficient composition follows from
`etaleSystemProjection_coherence`. No further invertibility or coherence hole is added.

Added `EtaleCofinalExtensionExistence`, `EtaleCofinalBlockFactorization`, and
`EtaleCofinalSupportEvaluation`, with matching nodes and detailed sourced proof texts.
The first two contain the remaining geometric construction obligations; the third has
a complete Lean proof. The original node records this assembly. No existing dependency,
source-library declaration, target, definition, instance or global attribute was changed.

Removed the item's old transparency-disabling options. Local irreducibility attributes
keep the sequence rings and `CofinalRepeatSupport.kappa` abstract; public transparency is
unchanged. Compilation uses the prescribed launcher. The final clean file compiles took 17.8 s
for evaluation, 19.8 s for realization, and 20.4 s for the unchanged direct consumer
`EtaleSystemCofinalMate`. The temporary consumer copy was removed after this check.

## Proved and sorry left

This is a decomposition: one original hole closed and two lower holes added, for net
minus one hole closed. It is not a complete proof of geometric realization.

The original theorem
`AlgebraicGeometry.Etale.SystemProjection.etaleCofinalSupport_realization` has no
remaining `sorry`. The restriction compositor, support-comparison normalization,
levelwise reflection argument and support-evaluation calculation are complete.

The added theorem
`AlgebraicGeometry.Etale.SystemProjection.etaleCofinalSupport_evaluation`, node
`lem-pur-etale-cofinal-support-evaluation`, is proved without a local hole.

Every remaining hole is the entire proof of one of these public theorems:

- `AlgebraicGeometry.Etale.SystemProjection.etaleCofinalExtension_nonempty`, node
  `lem-pur-etale-cofinal-extension-existence`: normalized selected extension on one scheme.
- `AlgebraicGeometry.Etale.SystemProjection.etaleCofinalBlockFactorization`, node
  `lem-pur-etale-cofinal-block-factorization`: a simultaneous geometric presentation,
  repetition and factorization of supplied local selected extensions, and their three
  evaluation diagrams.

The first statement has no morphism, compactification or support functor. The second
has no selected-extension/support comparison, coefficient-projection invertibility,
projection composition law or cofinal support evaluation conclusion. The assembly
constructs that comparison and proves its normalization and evaluation. Neither lower
statement is the original existence assertion under another name.

Edge cases considered: identity and shifted subsequences, skipped indices, equal
successive least selected indices, and finite torsion coefficients with nonflat maps.
The least index t(m) exists for every natural-number order embedding; t(r(i))=i and
its nonempty fibers are finite. No new flatness, cartesianness, boundedness, or
compact-support right-adjoint assumption is imposed.

There are no holed definitions. The local extensions carry ordinary adjunctions and
normalized total-derived universal properties; their comparisons are determined by
units and universal cochain counits. Repetition is prescribed on sections, maps and
restrictions, and its geometric comparisons on sections. The existential proof chooses
presentations subject to these normalizations; it defines h by the actual comparison
word, rather than choosing an unspecified support comparison.

## No longer needed

Removed direct proof imports from the item:
`Sheaf.CategoryTheory.SystemEvaluationKFlat`,
`Sheaf.CategoryTheory.SystemSelectedDerivedExtension`,
`Sheaf.CategoryTheory.SystemOrdinarySelectedExtension`,
`Sheaf.Paper.SystemBlockRepetition`, and
`Sheaf.CategoryTheory.SystemLevelLeftExtension`.
The redundant direct coefficient-projection import was also removed; CofinalData
publicly provides it. BlockFactorization is available through SupportEvaluation.

Their planned nodes remain needed by the two lower construction statements:
`lem-pur-system-evaluation-kflat`, `lem-pur-system-selected-derived-extension`,
`lem-pur-system-ordinary-selected-extension`, `lem-pur-system-block-repetition`,
`lem-pur-system-level-left-extension`, and `lem-coef-semilinear-derived-sections`.
They are moved dependencies, not pruned mathematical work. The new nodes record their
uses. No module or node is claimed globally unnecessary and no withdrawal is proposed.

## Where the brief, the DAG or earlier work was wrong

Read the current server queue, rework row, claim and older build-error record. The
current assignment is a stage-3 proof row with one hole. The old build error concerned
imports of EtaleSystemCofinalData and EtaleSystemCoefficientProjection; the unchanged
original item compiled against the available published artifacts. This was not treated
as permission to withdraw its statement.

The old node combined the entire realization into one step. Existing dependencies do
not directly provide the normalized transfer of selected extension to the actual
sequence-site interface or its simultaneous block factorization. Those are the two
remaining construction obligations. The final diagram calculation is now proved.

A draft claiming literal section identities for an arbitrary projection theory was too
strong: an arbitrary chosen open left adjoint may have different underlying carriers.
The delivered block statement instead chooses a simultaneous geometric presentation,
and explicitly records the factor and repetition evaluation diagrams. It does not
claim that arbitrary open-adjoint choices have identity maps on sections.

A read-only dependency traversal also encountered an inherited DAG cycle among
`lemma-weil-pbc-derived-exchange-replacement`,
`lem-weil-pbc-derived-exchange-termwise`, and
`lem-weil-pbc-derived-exchange-bounded-comparison`. This delivery does not change
those nodes or their edges.

The existing node's created.item is a module name, so the blueprint ancestor helper
returns None. The new nodes record the actual ancestor
`def-weil-exceptional-inverse-image` and the cofinal-mate chain. Its adic-stage route is
preserved; no realized statement or proof step of the unit is bypassed.

## New nodes

`lem-pur-etale-cofinal-extension-existence` records the local sequence-site extension
with ordinary unit and derived cochain normalizations. It follows Zheng 4.1 and the
existing ordinary/derived selected-extension and K-flat evaluation declarations.

`lem-pur-etale-cofinal-block-factorization` records a simultaneous geometric projection
presentation, block repetition, factorization of local selected extensions, and the
three explicit evaluation diagrams used by the support comparison. It uses the existing
block and semilinear geometry and normalized tensor extension.

`lem-pur-etale-cofinal-support-evaluation` records the proved categorical calculation
from these diagrams and the coefficient evaluation equation. All geometric data and
the comparison normalization are hypotheses; its conclusion is an equality only.

Mathlib and source-library searches found categorical and tensor machinery but no
complete match for these normalized sequence-site constructions. No change record is
needed: only the assigned module, its node, and the three new modules/nodes are changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.EtaleCofinalBlockFactorization": "5ac61bbddd54e30ee9f294b631eab5c944a3b9b2", "Sheaf.Paper.EtaleCofinalExtensionExistence": "eb99ccdc910b166ce3050789d19eddb35edcdd15", "Sheaf.Paper.EtaleCofinalSupportEvaluation": "bf6ca98580486e0f66e19d277d14c0d7698fdfd6", "Sheaf.Paper.EtaleCofinalSupportRealization": "871260d88349e387731bcfdb7c6289943f2b5917"}, "results": {"Sheaf.Paper.EtaleSystemCofinalMate": {"hash": "35ffc1a3876fb6fd8c6408d2029405d2abe2c6d1", "status": "OK"}}, "seconds": 65, "time": "2026-10-28T01:15:43+0800", "transitive": 0, "version": 1}
```

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
