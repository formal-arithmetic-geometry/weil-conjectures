## What changed
Added two intermediate theorem modules reducing the target to finite closed-cover induction and dimension induction, and proved both target declarations from these named intermediate statements and existing 02UX/closed-immersion declarations. Added proof-only imports.

## Proved and sorry left
`TopCat.noetherian_vanishing_irreducible` and `TopCat.noetherian_vanishing_of_irreducible_components` are proved. `TopCat.cohomology_vanishing_of_finite_closed_cover` remains sorry (node `new-node-finite-closed-cover-cohomology-vanishing`). `TopCat.irreducible_integer_extension_vanishing` remains sorry (node `new-node-irreducible-integer-extension-vanishing`).

## No longer needed
No imports or existing nodes were pruned.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt only restated the target and made no reduction. This delivery separates the finite-cover and integer-generator steps as strict intermediate statements and combines them in a compiled proof.

## New nodes
`new-node-finite-closed-cover-cohomology-vanishing` and `new-node-irreducible-integer-extension-vanishing` are the two unresolved strict steps described above.

## Earlier second reading (a previous round; superseded)
The compiled reduction uses finite irreducible closed covers, the existing 02UX extension-by-zero reduction, and closed-subspace dimension monotonicity. The two remaining sorries are strict intermediate steps with independent nodes and complete proof descriptions.

Change record: `coord/changes/noetherian-vanishing-proofs.md`.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered target module with the repository version. Existing theorem signatures are unchanged byte for byte; only proof imports, private reduction code, and proof bodies differ. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`; they compile without errors. The two remaining `sorry`s are named theorems with docstrings and matching DAG nodes. No forbidden declarations or hollow definitions were added. Verdict: pass.
3. Checked both split statements against Proposition 02UZ and tested their edge cases in the docstrings: empty cover, q=0, empty open, d=0, and proper closed complement. They are strict intermediate reductions, not restatements of the item. Mathlib and local searches found no existing theorem. Verdict: pass.
4. The fixed-bound finite-cover helper and strong dimension induction preserve the unit route through 02UX, open-closed cohomology, closed-pushforward comparison, and constant acyclicity. Proof-only imports are private. Verdict: pass.
5. Updated both new node records so their proof steps, proof dependencies, sources, and Lean signatures match the delivered declarations. No old proof dependency was pruned. Verdict: pass.

Changed the second-reader binder normalization was reverted to preserve the existing target interface; added the missing proof-only imports, corrected the intermediate node records and proof descriptions, and removed the unused change record.

## Second reading by P1

1. Compared the delivered target module with the repository version using `diff`. Existing theorem signatures are byte for byte unchanged; the delivery adds only proof-only imports, a private helper, and proof bodies. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`; all compile cleanly. The only remaining `sorry`s are the two named public split theorems, each documented and represented by a DAG node. No forbidden declarations or hollow definitions were added. Verdict: pass.
3. Checked both split statements against Proposition 02UZ and their Lean signatures, including empty covers, degree zero, empty opens, dimension zero, and proper closed complements. They are strict reductions and do not restate either target. Searches recorded in the node files found no existing declarations. Verdict: pass.
4. The proof follows the unit route through finite irreducible closed covers, 02UX extension-by-zero reduction, open-closed cohomology, closed-pushforward comparison, and constant acyclicity. The three added imports in the target are proof-only; no unused imports or old proof dependencies were identified for pruning. Verdict: pass.
5. The target node proof and dependencies agree with the delivered code, and both new node records match their Lean declarations, sources, proof descriptions, and dependencies. Verdict: pass.

Changed nothing during this second reading; the delivered proofs and split statements were already correct and compiled.
