## What changed
Added the component transport theorem `ModuleCat.localizedTensorComparisonProperty_shift_component` as a named intermediate statement with a documented proof obligation. The target theorem now unfolds the localized comparison predicate and applies this component theorem for each representative, model, and degree.

## Proved and sorry left
The target theorem `ModuleCat.localizedTensorComparisonProperty_shift` is proved by complete Lean code from the component theorem. The component theorem `ModuleCat.localizedTensorComparisonProperty_shift_component` remains `sorry` and is recorded as node `lem-pc-localized-tensor-comparison-shift-component`.

## No longer needed
None; the original proof import remains the only imported module.

## Where the brief, the DAG or earlier work was wrong
The DAG treated the full transport argument as one indivisible proof. It requires a component-level transport statement to make the predicate-level assembly explicit.

## New nodes
`lem-pc-localized-tensor-comparison-shift-component` in `dag/nodes/sec-picard-framework/lem-pc-localized-tensor-comparison-shift-component.json`.

## Earlier second reading (a previous round; superseded)
The second reader should check the component statement and the predicate unfolding assembly.

## Second reading by J2

1. I compared the delivered module with the repository version. The existing target declaration and its statement are byte-for-byte unchanged; the delivery adds only the documented component theorem and the target proof.
2. I compiled the module with `lcompile.py`; it succeeds. The only remaining `sorry` is the named component theorem, and there are no forbidden declarations or hollow definitions. The target proof itself is complete.
3. I checked the component statement against the predicate definition and existing localized comparison declarations. It is a genuine fixed-representative/model/degree transport obligation, with no weaker conclusion or added assumption; the searched library contains no duplicate theorem.
4. The target proof unfolds the predicate and applies the component theorem for exactly the required data. The import is still needed for the predicate and model declarations, and no imports or proof dependencies can be pruned. The unit route is preserved because the target remains realized through the component transport step.
5. The DAG nodes agree with the Lean declarations, statements, proof dependencies, sources, and blueprint links. The component node documents its proof obligation and is the sole split-off hole.

I changed only this report section; no Lean or DAG repair was needed after compilation and comparison.
