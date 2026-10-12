## What changed
Added two intermediate theorem modules and used them to reduce the target theorem to a real composition of the core normalized-data construction and its geometric-point lifting clause. The target module imports both proof-only modules.

## Proved and sorry left
`exists_constructible_module_normalized_generic_data` is proved by combining the two intermediate theorems. `exists_constructible_module_normalized_generic_data_core` remains sorry in node `new-normalized-generic-data-core`; `normalized_generic_data_lifts` remains sorry in node `new-normalized-generic-data-lifts`.

## No longer needed
No imports were removed. The detailed lower-level dependencies in the original DAG plan are encapsulated by the two intermediate nodes and need not be imported directly by the target module.

## Where the brief, the DAG or earlier work was wrong
The original four-step proof plan requires substantial normalization, sheaf comparison, and algebraic-extension glue that cannot be completed in this item window. These are strictly separated into the core construction and geometric lifting statements.

## New nodes
`new-normalized-generic-data-core`: core existential data, stated in `NormalizedGenericDataCore.lean`.

`new-normalized-generic-data-lifts`: geometric-point lifting clause, stated in `NormalizedGenericDataLifts.lean`.

## Earlier second reading (a previous round; superseded)
The target proof combines the core existential and lifting statements by direct elimination and refinement. Both new statements are strictly smaller parts of the target and preserve its unit route; their remaining proofs are explicit named nodes.

## Second reading by N2

1. **Statements unchanged.** Compared the delivered target module against the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only its proof and proof-only imports changed. Verdict: pass.

2. **Proof and axioms.** Compiled all three delivered modules with `lcompile.py --all`. The target theorem is proved; the only remaining `sorry`s are the two explicitly named split-off theorems, each with a matching DAG node. No definitions contain `sorry`, and the delivered files introduce no `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. Verdict: pass subject to the two declared split nodes.

3. **Split-off statements.** Checked `exists_constructible_module_normalized_generic_data_core` (the existential normalized data without the lifting conjunct) and `normalized_generic_data_lifts` (the lifting conjunct for supplied normalized data). Each is a strict component of the target, has a source docstring, and has a corresponding node; neither duplicates a library declaration. Verdict: pass.

4. **Pruning and route.** The target now takes the direct composition of the core construction and lifting clause. The former low-level imports are no longer required by this proof and are replaced by proof-only imports of the two split modules. The normalized generic-data construction and lifting route remains the unit route. Verdict: pass.

5. **DAG agreement.** The two new node records match the declarations, modules, and remaining `sorry`s, and the target node records the reduced proof dependencies. Verdict: pass.

Changed the report only during this second reading; no Lean statements or definitions required repair.
