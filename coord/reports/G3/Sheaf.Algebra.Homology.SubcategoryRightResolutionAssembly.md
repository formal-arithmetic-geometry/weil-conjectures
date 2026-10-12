## What changed

Proved `CochainComplex.exists_complex_of_cokernel_pushout_system` in
`Sheaf.Algebra.Homology.SubcategoryRightResolutionAssembly`, without changing its
signature, visibility, or docstring. Added the proof-only import
`Mathlib.Algebra.Homology.Embedding.HomEquiv` for restriction and extension by zero.
Updated the existing node's proof to record the actual Mathlib constructions.
No definitions or other modules changed.

The supplied factorizations prove the square-zero and augmentation identities.
The natural-number complex is extended by zero to integer degrees. Cokernel
uniqueness identifies the resulting opcycles with the supplied Q objects and
transports the pushout squares. Below the bound, one uniform square with an
identity right leg handles both the boundary and all smaller degrees.
Membership is proved using the actual extension terms, without assuming that the
specified set is invariant under isomorphism.

## Proved and sorry left

Closed the only original hole:
`CochainComplex.exists_complex_of_cokernel_pushout_system`
(node `lem-weil-pbc-subcategory-right-resolution-assembly`).
No sorry remains in the item, and no holes were added or split off.
The complete proof uses Mathlib, with no Sheaf proof dependencies.
Single-file compilation passes without warnings. The required delivery dry run
checks the declaration's axioms and unchanged signature.

## No longer needed

No imports removed. No planned nodes or modules pruned: the original dependencies
`def-weil-abstract-derived-category` and `def-weil-pbc-category-colimit` describe
notions supplied by Mathlib and are still used. No unit statement or step is bypassed.
No new lemma modules were necessary.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox module was empty; it was replaced from the repository.
The DAG's below-bound argument need not distinguish a-1 from smaller degrees:
zero opcycles and an identity right leg give one uniform pushout construction.
This is a simplification of the existing argument, not a statement change.

## Second reading by G3

1. Compared the delivered module against the repository with `diff -u` and a
   byte comparison of the entire declaration signature. PASS: the only Lean
   changes are the original theorem's proof and one plain proof-only import.
   The signature, visibility, definitions, and existing docstring are unchanged;
   no change record or forced adaptation is needed.
2. Compiled the delivered file locally through `lcompile.py`: PASS, no warnings
   or errors (3.8 seconds). Compiled a scratch copy with `#print axioms` for
   `CochainComplex.exists_complex_of_cokernel_pushout_system`: exactly `propext`,
   `Classical.choice`, and `Quot.sound` (3.3 seconds). Scanned the delivered Lean
   for sorry and forbidden declarations: none. The complex is constructed with
   `CochainComplex.of` and extension by zero; the only chosen isomorphisms come
   from proved cokernel uniqueness, not unproved existence.
3. PASS: no statements were split off, no new declarations or nodes were added,
   and no holes remain. Read the square-zero, augmentation, cokernel and pushout
   arguments independently. Checked m=0, n=a-1, and n<a-1: the initial projection
   is an isomorphism, the incoming term is zero, and the uniform lower pushout
   with identity right leg handles both boundary and smaller degrees. Membership
   uses the actual extension objects, so no isomorphism-invariance hypothesis on
   the set is silently assumed.
4. PASS: read the proof from its conclusion back to the supplied system. Searched
   the library and upstream homology modules for assembly and resolution results;
   no applicable shorter assembly theorem was found. Read Mathlib's extension
   definition, which selects the supplied term or the chosen zero object. The
   existing public import supports the signature; the added HomEquiv import is
   needed only by the proof. No old proof dependency becomes unused: complex
   constructions and colimit universal properties remain essential. Read
   `dag/units/sk-thm-p1.json`, including `realized`: this auxiliary assembly node
   bypasses none of its statement or step realizations. No pruning is claimed.
5. PASS: compared the existing and delivered node JSON. Only `proof` and
   `proof_origin` changed. The four steps describe the actual extension,
   augmentation, cokernel identifications, and lower pushouts. Their `uses`
   union agrees with the unchanged `proof_deps`. The node's statement and Lean
   record stay unchanged; no new-node checks apply.

Second reading changed only this report: no repair of the Lean proof or node
was necessary. Closed one original hole, added zero holes; this is a complete
proof, not a decomposition. The scratch axiom probe is outside delivered lean/.
