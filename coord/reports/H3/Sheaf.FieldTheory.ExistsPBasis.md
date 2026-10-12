## What changed

Proved `Field.exists_p_basis` by applying `FieldTheory.exists_pBasis_extension` to the empty family over `ZMod p`. The empty family's sole bounded monomial is shown linearly independent, and the resulting basis is returned with the extension's indexing. Added a proof-only import of `Sheaf.FieldTheory.PBasisExtension`.

## Proved and sorry left

Closed the local hole `Field.exists_p_basis` (1 of 1). No `sorry` remains in the delivered module; holes added: none; statements split off: none. This is a reduction to the existing open theorem `FieldTheory.exists_pBasis_extension` (node `lem-weil-pbc-p-independent-extends-to-p-basis`), not an axiom-free proof of the target: its axiom closure still contains `sorryAx`. No object is defined by choosing an arbitrary witness from that theorem; its witnesses are eliminated only to prove this existential proposition.

## No longer needed

All four original direct proof dependencies are removed: `def-weil-field`, `lem-weil-pbc-zorn-lemma`, `def-weil-algebraic-element`, and `lem-weil-pbc-simple-algebraic-extension-power-basis`. The field definition remains a statement dependency. The extension theorem still uses the three argument lemmas in its own DAG plan, so no claim of global pruning is made. No original import or module was removed; the original Mathlib imports support the public signature and prime-field instances.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was substantially longer than necessary: the existing p-basis extension theorem already packages the maximality argument, so specializing it to the empty family gives the target directly.

## New nodes

None.

## Second reading by H3

1. Compared the only delivered module with the repository version. Its existing
   declaration signature, universe, local ZMod instance, public visibility, and
   docstrings are byte for byte unchanged. The sole changes are the proof body
   and the plain, proof-only import of `Sheaf.FieldTheory.PBasisExtension`.
   No definition or target statement changed; no change record is required.
2. Compiled the module locally through `lcompile.py`: clean, no warnings (47.5 s).
   Read the proof: the exponent functions on Empty are all zero, and a finite
   linear combination of their sole monomial 1 reduces to its single coefficient.
   The extension theorem applies over ZMod p with exactly the required coefficient
   field. Its J is in the field's universe; Empty ⊕ J has the required universe.
   The returned basis and evaluation identity prove the original existential.
   No sorry, axiom, unsafe, opaque, extern, implemented_by, or hollow definition
   occurs in the delivered module. A scratch-copy `#print axioms` check is recorded
   below: both `Field.exists_p_basis` and `FieldTheory.exists_pBasis_extension`
   use exactly `[propext, sorryAx, Classical.choice, Quot.sound]` (scratch compile
   clean, 2.2 s). The existing open extension theorem is an allowed remaining dependency.
3. No new statements or split-off holes exist. Read the full statement of the
   imported extension theorem and its DAG node: it is genuinely stronger, preserving
   an arbitrary initial p-independent family. Specializing to Empty is valid also
   for p = 2, perfect fields, and arbitrary field universes; no finite-generation
   hypothesis is used. No additional statement or arbitrary data choice is hidden
   in this reduction.
4. Searched `lean/Sheaf` and `lean/WeilConjectures` for exists_p_basis,
   exists_pBasis, and pBasis_extension: the existing extension theorem is the
   shortest general library route found. Read Mathlib's singleton/subsingleton
   independence lemmas in LinearIndependent/Basic.lean: they can shorten the empty
   family subproof with an additional proof import, but the current correct proof
   needs no such import and was retained. Also searched Mathlib's SeparablyGenerated
   and PurelyInseparable sources for p-basis/p-independence; no direct match found.
   Read dag/units/sk-thm-p1.json: neither this helper nor its old proof dependencies
   realizes a unit statement or step, so the shortcut is below the unit level and
   preserves its route. Completed No longer needed with def-weil-field and clarified
   that no module is globally pruned.
5. Found and repaired the stale six-step Zorn proof in the delivered DAG node.
   Its three current steps now match the Lean: empty-family independence, extension
   over the prime field, and returning the combined family's basis. The union of
   their uses equals proof_deps, containing only the extension node. proof_origin
   names the actual library theorem. Restored every other node field from the
   repository; no new nodes or statement changes. The node's Lean statement remains
   unchanged.

Second reading changed metadata and report only; the correct Lean proof was retained.
