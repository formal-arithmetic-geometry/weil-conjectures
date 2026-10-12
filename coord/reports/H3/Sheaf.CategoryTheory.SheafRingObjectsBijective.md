## What changed
Split the bijectivity proof into two strictly simpler intermediate theorems, then combined them by constructor. Added imports for the two component modules.

## Proved and sorry left
Proved `CategoryTheory.sheafRingObjects_bijective` from `sheafRingObjects_injective` and `sheafRingObjects_surjective`. Left `CategoryTheory.sheafRingObjects_injective` and `CategoryTheory.sheafRingObjects_surjective` as named sorries in new modules, with corresponding DAG nodes.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The original proof plan contains substantial independent injectivity and surjectivity arguments; these are represented as separate intermediate nodes so the top theorem compiles from them.

## New nodes
`lem-weil-pbc-sheaf-ring-objects-injective` and `lem-weil-pbc-sheaf-ring-objects-surjective`.

## Second reading by H3

1. **Module comparison and statements:** Compared the delivered bijective module against the repository version. The target theorem signature is unchanged; only proof imports and proof text were added. The split node records were corrected to match their actual injective and surjective conclusions.
2. **Compilation and axioms:** Compiled all three modules with `lcompile.py`; compilation succeeds. The two component theorems remain the explicitly named split-off `sorry`s, while the top bijectivity theorem is proved by pairing them. No forbidden declarations or hollow definitions were introduced.
3. **Split statements:** Checked the component statements against their Lean declarations and the sectionwise reconstruction source. They are strictly simpler injectivity and surjectivity components, each needed by the final constructor; no duplicate library theorem was found.
4. **Pruning and imports:** The top proof uses both component modules, so their plain proof imports are needed. The shared Mathlib imports remain public because they support the theorem signatures. No unused import or obsolete proof dependency was identified.
5. **DAG and unit route:** Updated each node's prose, declaration, and verbatim Lean signature to agree with the delivered code. The unit route remains the original bijectivity step realized through the two component nodes.

Changed the two split node records to remove the incorrect bijection conclusion and stale theorem signatures; no Lean source proof changes were required.
