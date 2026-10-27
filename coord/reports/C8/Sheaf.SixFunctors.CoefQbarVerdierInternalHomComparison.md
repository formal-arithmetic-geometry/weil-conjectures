## What changed

Replaced the hole in `WeilConjectures.CoefQbarVerdier.internal_hom_comparison_exists`
by an explicit construction and a proof assembling finite-stage and scalar squares.
The original signature, docstring, and public import are unchanged. Its new proof
import is `Sheaf.SixFunctors.CoefQbarVerdierHomComparisonExtension`.

Added `CoefQbarVerdierHomComparisonComponents`: the common-stage Hom representative
formula proves naturality of `homToStage`; evaluating at the original field and
removing both self transitions by the actual scalar unitor gives
`stageHomInclusion`. Composing the finite Hom identification with the recorded
B.comparison and B.omegaComparison gives `localComparison`. Its values on literal
objects define `component`, and `component_naturality_stage` is proved.
All objects, maps and inverses are actual constructions, with no new choice from
an unproved existence statement.

Added `CoefQbarVerdierHomComparisonExtension`, which isolates only compatibility
of these fixed components with isoToStage. The main proof factors an arbitrary
representative through two stage isomorphisms and one finite-stage arrow, proves
the inverse square by cancellation, and composes the three naturality squares.
The definition of the comparison and all finite-stage naturality are outside
this remaining obligation. The unit route is retained.

Validation: all three delivery modules compiled together in import order with
no warnings or errors, taking 29.3 s, 6.9 s, and 8.1 s respectively. Repeated-field
inputs are handled using the genuine scalar unitor, rather than treating the
self transition as definitionally the identity. No existing module besides the
assigned item is changed; no existing public interface is changed.

## Proved and sorry left

This is a decomposition, not a net hole closure: one upper hole closed, one
strictly smaller scalar-square hole added. Net hole change: zero.

Closed: `WeilConjectures.CoefQbarVerdier.internal_hom_comparison_exists`
(node `lem-coef-qbar-verdier-internal-hom-comparison`). The assigned module now
contains zero holes.

Added and remaining: `WeilConjectures.CoefQbarVerdier.HomComparison.component_extension`
(node `lem-coef-qbar-verdier-hom-comparison-extension`), the sole `sorry` in the
delivery. It concerns only canonical changes of finite field for the constructed
components. It asserts neither a natural-isomorphism existence result nor
naturality for arbitrary morphisms.

Proved supporting results include `HomComparison.homToStage_naturality`,
`HomComparison.allPairs`, `HomComparison.selfCompositum_le`, and
`HomComparison.component_naturality_stage`, plus the private generic categorical
cancellation and assembly lemmas. Every new definition is hole-free.

## No longer needed

No existing import or module is withdrawn. No global pruning is claimed.
The old broad proof dependency list is replaced by the two actual new nodes;
its finite scalar and coefficient-category ingredients are still needed by those
nodes and by the existing data and operations. In particular none of
`lem-coef-rational-operations`, `lem-coef-integral-finite-extension`, or
`def-weil-algebraically-closed-coefficients` is claimed globally unnecessary.
No proof-only import of an unused dependency was added.

## Where the brief, the DAG or earlier work was wrong

The live server queue labels this a stage-3 proof item with one hole and no
current build-error report. The old rework row records a transitive coefficient
import failure; the current item source is present and all delivered modules
compile against the published dependencies. No quarantine archive was removed.

The original proof paragraph combined three tasks: constructing the components,
proving finite-stage naturality, and checking the scalar square. The first two
are now written and proved. Only the scalar square remains, as a named theorem
with its own precise statement, source, complete proof in words, and DAG node.
There is no statement weakening or change to a target or upstream declaration.

## New nodes

`def-coef-qbar-verdier-hom-comparison-components` owns the explicit finite-stage
Hom inclusion isomorphisms, local dual-to-Hom comparisons, and literal components,
including their proved finite-stage naturality. All its declarations are in
`Sheaf.SixFunctors.CoefQbarVerdierHomComparisonComponents`.

`lem-coef-qbar-verdier-hom-comparison-extension` states only the remaining scalar
square for those components, in
`Sheaf.SixFunctors.CoefQbarVerdierHomComparisonExtension`. Its proof follows the
retained finite-Hom scalar argument. The generic specified-Hom scalar evaluation
and coherence node is declared as a tool use in its split report.

No change record is needed: only the assigned module, two new modules, its node,
and the two new nodes are delivered. No other existing file is adapted.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarVerdierHomComparisonComponents": "50c2303f28830e57a23f5511fe5036681f686ea6", "Sheaf.SixFunctors.CoefQbarVerdierHomComparisonExtension": "98eab61811233e6a2a3224712b04fa3832c2ddc9", "Sheaf.SixFunctors.CoefQbarVerdierInternalHomComparison": "23d04afbb597a934ec82ae792debddd7252c0743"}, "results": {"Sheaf.Paper.SfPackageExceptionalCoherenceRealization": {"hash": "06c4953b65e2b38aecc4c97dbca6c69edbac7b82", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierInternalHom": {"hash": "1d723423e9adea8fd21909e1a5684d1b675e0850", "status": "OK"}}, "seconds": 133, "time": "2026-10-28T00:59:20+0800", "transitive": 1, "version": 1}
```

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
