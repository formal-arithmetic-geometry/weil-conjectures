## What changed
Expanded the target proof by simp and reduced it to the named core compatibility theorem `etaleTensorOpenSectionIso_component_core`.

## Proved and sorry left
`etaleTensorOpenSectionIso_naturality` is proved. `etaleTensorOpenSectionIso_component_core` remains as one named sorry, with node `new-etale-tensor-open-section-core`.

## No longer needed
No imports or existing nodes were removed.

## Where the brief, the DAG or earlier work was wrong
The planned categorical mate calculation is isolated as the core theorem above.

## New nodes
`new-etale-tensor-open-section-core` records the lower component compatibility step.

## Second reading by Y3
1. Compared the delivered module with the repository version. Existing definitions and the target theorem signature are unchanged byte for byte; the only additions are the named core theorem and the target proof. Verdict: pass.
2. Compiled the module with `lcompile.py`; it compiles without errors. The target is proved, and the only remaining `sorry` is the named core theorem `etaleTensorOpenSectionIso_component_core`, recorded by node `new-etale-tensor-open-section-core`. Verdict: pass.
3. Checked the split-off statement against the expanded target. It is the strict component compatibility reduction obtained by unfolding `etaleTensorOpenSectionIso`, so it is true and needed rather than a restatement. Searches found no existing theorem with this statement. Verdict: pass.
4. Checked the proof route and imports. The target is reduced by `simpa [etaleTensorOpenSectionIso]` to the core compatibility statement; the canonical comparison and unit route from the unit are retained. No import is unused. Verdict: pass.
5. Checked the DAG node against the Lean declaration, including statement, proof dependencies, source, and unit. The unit route remains realized. Verdict: pass.

Changed only the target proof and added the named core theorem and its DAG node; no existing statement or definition was altered.
