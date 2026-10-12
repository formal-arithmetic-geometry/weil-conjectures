## What changed

Repaired the landing refusal by deleting all three duplicate private declarations:
`stalk_map_smul`, `nonvanishingLocus_iso`, and `tensorPow_iso`.
Added proof-only `import all Sheaf.AlgebraicGeometry.AmpleIso`, which allows direct use
of its existing private `tensorPow_iso` and `nonvanishingLocus_iso` theorems.
The latter already uses the existing `stalk_map_smul`; no copy is needed.
The target signature and all other modules remain unchanged.
Restored the returned delivery from the archived reviewer packet because the sandbox
initially contained only brief markers. Updated its DAG proof route to name AmpleIso.
Compilation through lcompile.py passes without warnings.
The delivery dry run rebases its generated commit onto the fetched sheaf-dag base.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.Modules.exists_tensorPow_section_nonvanishing_pullback`
(node `lem-weil-pbc-tensor-power-section-nonvanishing-pullback`).
Added 0 holes; no sorry remains in the delivered Lean module.
This is a proof from existing declarations; their transitive holes are unchanged.

## No longer needed

Removed the direct original proof import
`Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
(node `lem-weil-pbc-invertible-pullback-tensor`): it is used through
`Sheaf.AlgebraicGeometry.NonvanishingTensorPullback`.
The direct planned dependency `lem-weil-pbc-tensor-over-quotient-ring`
(Mathlib tensor quotient/base-change lemmas) is also encapsulated by that criterion.
`def-weil-pbc-ample-invertible-module` remains through the public statement import
`Sheaf.AlgebraicGeometry.Ample`, but is not a separate proof dependency.
The three copied private helpers are pruned and replaced by existing AmpleIso proofs.
No module is claimed to leave the global targets import closure.

## Where the brief, the DAG or earlier work was wrong

The previous delivery incorrectly assumed private helpers could not be imported.
Lean's module system supports `import all`, already used elsewhere in this library.
This repairs the exact landing refusal by importing and applying existing proofs,
without redeclaring them or changing their visibility or signatures.
The auxiliary node is below the unit level; the unit's realized route is preserved.

## Second reading by A3

1. Compared the delivered Lean module with the repository version. The theorem
   signature is byte-for-byte unchanged; only its proof and proof-only imports differ.
   Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. There are no
   local `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations.
   The remaining `sorryAx` reported by `#print axioms` is transitive from imported open
   work. Verdict: pass.
3. Checked the DAG node and searched the library and Mathlib search service. The proof
   uses existing AmpleIso helpers through `import all`; no duplicate split-off statement
   or new node was introduced. Verdict: pass.
4. The proof follows the existing unit route through pullback adjunction, tensor-power
   comparison, and nonvanishing pullback. The direct old imports and copied private
   helpers were pruned, and the node's proof and dependency fields match the code.
   Verdict: pass.
5. The target statement and all imported public interfaces remain unchanged; the node
   records the actual proof origin and dependencies. Verdict: pass.

Changed only the proof imports/proof body, the matching DAG proof route, and this report.
