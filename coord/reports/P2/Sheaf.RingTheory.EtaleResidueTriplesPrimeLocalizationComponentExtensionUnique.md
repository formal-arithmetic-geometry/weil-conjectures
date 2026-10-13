## What changed

Imported a new auxiliary theorem giving a global pointed model mapping epimorphically to a fixed local triple. The target uniqueness theorem now obtains this map, applies both compatibility hypotheses, and cancels the epimorphism.

## Proved and sorry left

The target theorem `etaleResidueTriples_primeLocalization_component_extension_unique` is proved. The new theorem `etaleResidueTriples_primeLocalization_component_extension_unique_aux` remains as one named `sorry`, containing the descent and epimorphic-model construction.

## No longer needed

No imports or planned proof dependencies were removed; the target uses only the new auxiliary theorem and the existing definitions.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated construction of a pointed affine model with an epimorphic map to the fixed local triple as elementary. It is a substantial descent statement, so it is split off explicitly as the auxiliary node.

## New nodes

`new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux`: existence of a compatible global pointed triple and epimorphic map to the fixed local triple.

## Earlier second reading (a previous round; superseded)

The target proof was compiled in the sandbox. The auxiliary theorem is the only remaining hole and corresponds to the pointed affine descent construction described in its docstring.

## Second reading by P2

1. **Statement preservation.** Compared the delivered target module with the repository version. The target theorem signature is byte-for-byte unchanged; only the proof and its private import changed. Verdict: pass.
2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py`. The target has no `sorry`; the sole remaining `sorry` is the named auxiliary theorem, and it is documented and represented by its DAG node. The target's axioms include only the permitted axioms plus `sorryAx` inherited from that auxiliary theorem. Verdict: pass.
3. **Split-off statement.** Checked the auxiliary theorem's signature against the construction it records: it asserts exactly existence of a compatible global triple and an epimorphic leg, with no weakened target conclusion or hollow definition. Its source, docstring, and node are present; no existing declaration duplicates it. Verdict: pass.
4. **Route and pruning.** The target follows the shortest available cancellation route after the auxiliary descent result. The public imports are required by the signatures, while the auxiliary theorem is imported privately for the proof. The unit route is retained and no obsolete dependency was identified. Verdict: pass.
5. **DAG agreement.** The target node records the auxiliary theorem as its sole proof dependency, and the auxiliary node records the exact Lean declaration and split status. Verdict: pass.

I changed only the target proof/import and added the auxiliary module, node, and report documentation; no statement or definition was altered.
