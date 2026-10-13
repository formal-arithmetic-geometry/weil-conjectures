## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMatching_chart_power_lift`
with a complete Lean reduction along the existing proof plan. The declaration's
signature and its public imports are unchanged. The proof establishes that f
belongs to the maximal ideal, chooses its finite generating family, prepends f,
and proves that the enlarged family still generates the ideal. It obtains a
formal chart realization, applies `FormalGlueing.h0_chart_power_lift` using the
Noetherian completion's flatness, and transports the resulting equation through
the chart linear equivalence. `map_pow` converts the structural scalar action
to the exact ring multiplication in the original conclusion.

Added proof-only imports of `PuncturedCompletionFormalGlueingChart`,
`FormalGlueingH0ChartPowerLift`, `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`,
and `Mathlib.Data.Fin.Tuple.Basic`. Added the new module
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionFormalGlueingChart`, which
states only the geometric chart/equalizer identification, without any power
lifting. Updated the original node's proof, proof dependencies and proof origin
and added the new node. No existing definitions or interfaces changed, and no
adaptations or change records are needed.

The geometric statement was checked against Stacks Tags
[0BLH](https://stacks.math.columbia.edu/tag/0BLH) (first two proof paragraphs)
and [05EL](https://stacks.math.columbia.edu/tag/05EL) (the compatible-section
module). The algebraic specialization follows
[05ER](https://stacks.math.columbia.edu/tag/05ER).

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.puncturedMatching_chart_power_lift`
(node `lem-sbc-punctured-matching-chart-power-lift`). No `sorry` remains in the
assigned module.

Added one hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_formalGlueingData_matching_chart`
(node `lem-sbc-punctured-completion-formal-glueing-chart`), in its own new module.
This is a decomposition, not a net decrease in holes: one closed, one added.
The new statement identifies H0 with the actual matching ring and one chart
module with the geometric chart sections, respecting restriction. It asserts
no numerator existence, no exponent and no localized surjectivity. The original
proof independently supplies the denominator lift using the existing algebraic
theorem, rather than applying a renamed copy of its conclusion.

The new hole is the entire proof of a named public theorem and has a complete
construction in its docstring and node. No data definition is chosen from it:
the existential datum and its specified linear identifications are eliminated
only inside the original theorem's proof. The only definitions in the delivery
are local explicit ring maps and scalar structures in that proof.

Edge checks: the new theorem needs no Noetherianity or flatness. Its finite list
is given together with its generating property. A nilpotent selected generator
has a zero chart module and empty geometric chart; the restriction identity is
then the equality of zero sections. Empty punctured spectra retain only the
completed matching coordinate. The case of an empty generating list is vacuous
because the new theorem asks for an index; the main proof prepends f, so its list
always has an index, even when the original family is empty. Redundant and zero
generators cause no exception. Local-ring instances already exclude the zero
base ring, but zero component section rings remain allowed.

Both modules were compiled with `lcompile.py`, including the original proof
against the sandbox's compiled new module. The final proof has no unfinished
goals. The delivery dry run printed OK: the complete set compiles and passes preflight
except for the second reading, which is reserved for the second reader. Nothing
was pushed.

## No longer needed

None. The original public import supplies the definitions in the unchanged
signature. The formal chart-power-lifting theorem remains necessary. All new
imports are used: the geometric bridge supplies the chart identifications, the
algebraic theorem supplies the power lift, the adic-completion import supplies
flatness, and the finite-tuple import supplies the enlarged generating family.
No unit statement or step is bypassed. No existing nodes or modules are claimed
pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's first two steps did not have a Lean interface exposing the geometric
chart coordinate. The existing
`exists_formalGlueingData_matching_projection` in
`PuncturedCompletionFormalGlueingData` exposes only the completed coordinate:
it provides no identification of a chart with its geometric sections and no
H0/matching-ring equivalence. Its signature therefore cannot supply the input
needed for `h0_chart_power_lift`. It is left unchanged. The new theorem records
the chart/equalizer part of the stated plan, keeping the existing algebraic
lifting result as the separate third step.

The generating family is prepended with f instead of appended, a reindexing
that makes the distinguished parameter definitionally equal to f and avoids
dependent casts of chart section rings. This does not change the route.

Lean's restricted scalar structures and nested scheme restrictions require an
explicit use of `c.map_smul` and a local transparency option. The proof has a
comment explaining its extra elaboration heartbeat allowance; file compilation
remains within the 60-second limit.

The local Stacks source checkout is absent; the cited official tag pages were
read directly. LeanSearch returned an Internal Server Error, recorded as
unavailable rather than evidence of mathematical absence. LeanFinder and grep
found single-scheme localization tools but no formal-H0/geometric-chart bridge.
Blueprint searches for formal glueing and matching sections returned no node
with this statement.

## New nodes

`lem-sbc-punctured-completion-formal-glueing-chart`:
`dag/nodes/sec-smooth-base-change/lem-sbc-punctured-completion-formal-glueing-chart.json`.
Its module is `Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionFormalGlueingChart`.
For a given finite generating family of the local maximal ideal and one index,
it states the linear identification of compatible tuples with the actual
matching ring, together with the linear identification of that chart and its
restriction identity. Source: Tags 0BLH and 05EL. Its proof constructs the
finite affine charts, their localization/tensor comparisons and overlap maps,
then applies the sheaf equalizer and the Spec-Gamma adjunction. The statement
is a geometric part of the original proof, independent of flatness and power
lifting. Search records reflect the actual LeanSearch failure, the eight
LeanFinder results and the zero Mathlib grep hits. No change records were added.

## Second reading by N1

1. Compared the delivered item module with the repository version. The theorem signature and existing declarations are unchanged; only proof-only imports and the proof body changed. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; no errors, warnings, forbidden declarations, or unfinished goals remain in the item theorem. The split theorem is the only intentional `sorry`, with its docstring and node. Verdict: pass.
3. Read the split theorem and checked edge cases described in its docstring (nilpotent and redundant generators, empty charts, and zero section rings). It is a strict geometric intermediate and does not restate the target or include denominator lifting. Verdict: pass.
4. Checked the proof route against the unit plan: finite generation, the formal-gluing chart realization, flat completion, and the existing chart power-lifting theorem are all used. No proof dependency was removed without justification; no shorter available library route was found. Verdict: pass.
5. Compared the DAG nodes with the Lean declarations and proof dependencies. The new node records its source, proof steps, searches, and split status; the target node records the actual imports and theorem used. Verdict: pass.

Changed only the proof and proof-only imports of the target, added the geometric intermediate module and node, and added this second-reading report. The dry-run delivery checks passed after this report update.
