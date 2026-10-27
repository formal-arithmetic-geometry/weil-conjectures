# SemilinearProperOpen consumer elaboration

## Reason

Three unclaimed direct importers exceeded the compile-time limit against the
reorganized intrinsic operations. The original clopen file took 65 seconds,
the ring-square file 90 seconds, and the graph file 73 seconds. Artifact-writing
checks exposed further costs after the initial proof-only checks passed.
All original public imports, manually written declaration headers and public
construction bodies are retained. No source-library module changes.

## Old

The private clopen model placed three large product equivalences directly in its
record, with reflexive restriction isomorphisms. All exact-localization, open-model
and gluing proofs were in one file. The final public theorem assembled its open
model record inline.

The ring-square module privately imported the entire mate module:

```lean
import all Sheaf.SixFunctors.SemilinearProperOpenMatePasting
```

The graph module used default automatic injectivity generation and contained both
its ordinary operations and its final derived-evaluation structure.

## New

The three private clopen equivalences have concrete definitions and proved forward
functor equations. They are locally irreducible after those equations are proved.
The private model transports insertion maps using explicit restriction isomorphisms;
naturality and inverse/hom cancellation prove the original normalization laws.

`DiagramOpenClopenShiftCore` retains the original public structures, shift instances
and generic exact-localization calculations. `DiagramOpenClopenShiftOpenSupport`
retains the original open-model and identity calculations. Its public theorem
`openModels_nonempty` proves existence by the original concrete open-model record
literal. The final theorem selects that fully proved witness; no data is selected
from an unproved existence statement. The original generic gluing calculations
remain beside the final clopen model. The original theorem statement is unchanged;
its open-model proof branch now uses this proved theorem. Moving the gluing proof
exposed a failed `simpa [j, hr] using hx` at the complementary-cover branch; an
explicit `change x ∈ Set.range z; rw [hr]; exact hx` proves the same fact.
Every other original
public header, construction body and proved public body is retained verbatim.

The existing operation-shift definition node follows the core. The open-model
construction receives its own proved node, and the existing final theorem node
records that proof dependency. Both support modules are publicly re-exported;
private helpers are imported with `import all`.

The ring-square module replaces only its private proof import:

```lean
import all Sheaf.SixFunctors.SemilinearProperOpenEvaluationSupport
```

All its declaration code and public imports remain unchanged.

The graph profile identified 15.3 seconds in generated congruence simp work.
`set_option genInjectivity false` avoids automatic injectivity declarations.
Writing its artifact still took 73 seconds, so the original ordinary operations
move verbatim to `SemilinearCompactifiedGraphData`, publicly re-exported by the
original module. Eleven existing helper theorem holes move with that data; the
one existing final theorem hole stays with the derived-evaluation structure.
The ordinary data file omits the three derived-only proof imports; the final file
retains them. All twelve holes, declaration names, statements, construction bodies and existing
proof bodies are retained. This is a layout change, not a proof or decomposition.
The graph module has no current direct Lean importers.

Final artifact and consumer checks are recorded in the delivery report.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagramOpenClopenShiftModels | unclaimed | Private equivalence API and proved open-model witness. |
| Sheaf.Paper.DiagramOpenClopenShiftCore | new | Original structures and generic exact-localization calculations. |
| Sheaf.Paper.DiagramOpenClopenShiftOpenSupport | new | Original open-model calculations and proved witness theorem. |
| Sheaf.SixFunctors.SemilinearEvaluationRingSquare | unclaimed | Import private evaluation API. |
| Sheaf.Paper.SemilinearCompactifiedGraphEvaluation | unclaimed | Re-export ordinary graph data; disable automatic injectivity generation. |
| Sheaf.Paper.SemilinearCompactifiedGraphData | new | Original ordinary data and eleven existing helper holes. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Unchanged source checked against the new clopen artifact. |
| Sheaf.SixFunctors.SystemProperOpenScalarSquare | unclaimed | Unchanged source checked against the new clopen artifact. |
| Sheaf.SixFunctors.SemilinearEvaluationOrdinaryAdjunction | unclaimed | Unchanged source checked against the new ring-square artifact. |

## Status

landed 20261027T021259-L-2752245 2026-10-27 (merge of deliver/C2/Sheaf.SixFunctors.SemilinearProperOpenMatePasting)
