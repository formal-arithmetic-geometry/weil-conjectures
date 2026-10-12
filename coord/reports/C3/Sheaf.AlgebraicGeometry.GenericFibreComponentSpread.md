## What changed
Split the geometric proof into a clopen shrinking theorem and two trace inclusion theorems, then combined them with `Set.Subset.antisymm` in `exists_open_generic_fibre_component_spread`.

## Proved and sorry left
The target theorem `exists_open_generic_fibre_component_spread` is proved. The new declarations `exists_open_generic_fibre_component_spread_core`, `generic_fibre_component_spread_trace`, and `generic_fibre_component_spread_trace_reverse` remain sorry-backed geometric steps.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The original node had no usable Lean dependencies for the substantial Stacks argument, so it required explicit intermediate statements.

## New nodes
Created `lem-sbc-generic-fibre-component-spread-core`, `lem-sbc-generic-fibre-component-spread-trace`, and `lem-sbc-generic-fibre-component-spread-trace-reverse` for the strict substeps.

## Earlier second reading (a previous round; superseded)
The parent combines the two inclusions by antisymmetry; the new statements are strict substeps of the target and preserve the unit route.

## Second reading by C3

1. Compared the delivered target module with the repository version. The target statement and all existing declaration signatures are unchanged; only its proof and proof-only imports changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py`. There are no errors, axioms, unsafe declarations, or sorry outside the three explicitly named split theorems. Verdict: pass.
3. Read the split-off statements and their DAG nodes. The core and two trace inclusions are true strict substeps of the target, with Stacks Tag 055N sources and explanatory proof docstrings; they do not restate the target. Verdict: pass.
4. Checked the proof route and imports. The parent combines the core shrinking result and the two trace inclusions by `Set.Subset.antisymm`; the unit route through the shrinking and trace steps is retained. Verdict: pass; no unused imports were found.
5. Checked DAG/Lean agreement. Node declarations, modules, theorem names, statements, proof origins, and split status match the delivered files. Verdict: pass.

Changed the split theorem docstrings to provide complete proof sketches and removed a style warning; no mathematical statements were changed.
