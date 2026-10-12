## What changed

Proved `SymmetricAlgebra.degree_map_exists` directly using Mathlib:
`Submodule.map_pow`, `LinearMap.range_comp`, `SymmetricAlgebra.lift_ι_apply`,
and monotonicity of powers. The symmetric degree is the nth power of the range
of the canonical inclusion; the lifted map sends the source inclusion into the
target inclusion. This works also in degree zero and for zero modules and rings.
The proof uses no unproved project theorem. A declaration-local linter option
suppresses the existing unused existential proof binder `h`; its signature is unchanged.

Removed the earlier attempt's three component lemmas and their incomplete nodes,
and its unchanged sandbox copy of `Graded`. Restored `symmetric_degree_exact`
to its original statement, docstring and whole-proof sorry. No new modules or nodes.

Validation: the final proof compiled without warnings through `lcompile.py`.
`#print axioms SymmetricAlgebra.degree_map_exists` reported exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed: `SymmetricAlgebra.degree_map_exists` (one of two original holes).
Remaining: `SymmetricAlgebra.symmetric_degree_exact`, node
`lem-weil-pbc-symmetric-degree-exact`. Added holes: none. This is a partial proof,
not a decomposition. `degreeMap` still restricts the actual constructed lift,
using only the now-proved membership theorem.

## No longer needed

No existing import or dependency was removed. The public import of `Graded`
is preserved because it is part of the existing interface. The three unpublished
component nodes from the earlier attempt and their declarations were removed:
`lem-weil-pbc-symmetric-degree-exact-phi` / `degree_phi_exists_unique`,
`lem-weil-pbc-symmetric-degree-exact-surjective` / `degree_map_surjective`,
`lem-weil-pbc-symmetric-degree-exact-kernel` / `degree_phi_range_kernel`.
No landed node is pruned by this partial proof.

## Where the brief, the DAG or earlier work was wrong

The earlier decomposition had incomplete node statements and proof descriptions,
placed new holed statements in the item's module rather than separate modules,
and supplied an unauthorized second-reading section. Those changes were removed.

The initial dry run reproduced the earlier `ImportError`: `deliver3.py` imported
`refuse_missing`, then absent from `tools/import_cycles.py`. The final retry
printed OK after the tool became available. No worker repair or bypass was made.
The proof compiles and preflight passes except for the independent second reading,
which the second reader writes. Nothing pushed.

## Second reading by C3

1. **No accidental visible changes.** Compared the delivered module with the repository version. The declarations and signatures of `degree_map_exists`, `degreeMap`, and `symmetric_degree_exact` are byte-for-byte unchanged; the only proof-side changes are the body of `degree_map_exists` and its local linter option. No definition, target statement, or public interface was altered.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it compiles cleanly. The only remaining `sorry` is the named `symmetric_degree_exact` theorem. A scratch `#print axioms SymmetricAlgebra.degree_map_exists` reports only `propext`, `Classical.choice`, and `Quot.sound`; no forbidden declarations occur.

3. **Statements and split-offs.** No statements were split off and no nodes were added. The proved auxiliary theorem is true in degree zero and for zero modules as well as positive degrees: it follows from the image of the canonical inclusion, `Submodule.map_pow`, and monotonicity of powers. It is not a restatement of `symmetric_degree_exact` and does not weaken any target.

4. **Pruning and route.** The proof uses only the existing Mathlib symmetric-algebra constructions and elementary submodule lemmas. The existing `Graded` public import remains part of the module interface, and no proof dependency or unit-route node was removed. The proof does not bypass the unit's exactness statement; it establishes only the codomain restriction needed by `degreeMap`.

5. **DAG consistency.** The existing item node still names `symmetric_degree_exact`, whose statement and proof plan are unchanged. Since no new theorem with `sorry` or new module was introduced, no DAG node update is required. The module's remaining hole and the report agree.

Changed in this second reading: added this review section only; no Lean source or DAG content required repair.
