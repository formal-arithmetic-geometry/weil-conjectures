## What changed

Proved `Algebra.exists_separable_extension_reduction_tensorProduct_equiv_pi` in
`Sheaf.FieldTheory.GenericSeparableAlgebraSplitting`, preserving its signature, public imports,
and existing docstring. Added six proved private helpers for the Artinian decomposition,
reductions under surjective maps and equivalences, tensoring a reduction, reduction of a finite
product, and the final tensor-factor reassembly. Added proof-only Mathlib imports for Artinian
rings, tensor quotients and products, reduced quotients, and finite exponent bounds.

The argument uses the existing field-splitting declaration and Mathlib's packaged Artinian
Chinese remainder equivalence. Updated the node's proof and proof origin to describe the Lean
implementation; the four steps and their existing dependencies remain the same.

## Proved and sorry left

Closed the module's one hole:
`Algebra.exists_separable_extension_reduction_tensorProduct_equiv_pi`
(node `lem-weil-pbc-generic-separable-algebra-splitting`). No holes added or split off; no `sorry`
remains in the delivered module. All six private helpers are fully proved.

The theorem still uses the existing
`Algebra.exists_separable_split_purelyInseparable_prime_quotients` declaration; its own field
extension dependency is outside this delivery. This is a proof from the existing dependencies,
not a claim that the entire transitive import closure is free of holes.

## No longer needed

None. No original imports were removed, and all three existing proof-dependency nodes remain
needed. The finite-spectrum and CRT nodes are Mathlib leaves: `IsArtinianRing.quotNilradicalEquivPi`
packages their calculations, so no additional Sheaf module is needed for either.

No separate nilpotence-of-the-whole-nilradical theorem is needed: the proof uses the stronger
and simpler fact that the image of a nil ideal remains a nil ideal in a commutative algebra.
The field-splitting dependency's extra Galois and embedding conclusions are not used.

## Where the brief, the DAG or earlier work was wrong

No statement or unit-route error found. The old plan's global nilpotence exponent for the
nilradical is unnecessary; pointwise nilpotence suffices for the quotient reduction argument.
The finite-product proof does use a common exponent, supplied by finiteness of its index set.
The empty-product/zero-algebra case is handled by the same finite-spectrum construction.

During setup I mistakenly wrote temporary copies to the read-only repository, then restored
the original item and removed the temporary new file immediately. Subsequent work stayed in
the sandbox. Only the intended sandbox module and node copy are included in the delivery.

## Second reading by Y2

1. **Visible declarations:** Compared the delivered module with the repository version. The target
   theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only
   imports, private helpers, and the target proof were added.
2. **Compilation and axioms:** Compiled the module with `lcompile.py` successfully. The target's
   axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`s,
   axioms, unsafe declarations, or hollow definitions.
3. **Statements and dependencies:** The private helper statements are true reductions used by the
   proof and introduce no public split-off holes. The existing target statement remains unchanged
   and its proof uses the declared separable-splitting dependency; Mathlib supplies the Artinian,
   tensor-quotient, and finite-product facts.
4. **Pruning:** Checked the proof route for shorter available declarations. The Artinian CRT and
   quotient equivalences are the shortest Mathlib route, and all added imports are used by the
   helpers. No original import or proof dependency can be removed.
5. **Unit route:** The four DAG proof steps remain represented: Artinian reduction, separable
   residue-field splitting, transport through tensor/reduction, and finite-product reassembly.
   The unit's realized route and node statement are unchanged.

Changed during this reading: no Lean proof or statement changes; appended this review only.
