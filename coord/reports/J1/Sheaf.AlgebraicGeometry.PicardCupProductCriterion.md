## What changed

The target theorem now obtains the dual direct-image finite-local-freeness from
`picard_dual_directImage_isFiniteLocallyFree` and the cup-product equivalence from
`picard_cupProductCriterion_of_finiteLocallyFree`.  These are stated in the new
auxiliary module and are the two remaining geometric subarguments.

## Proved and sorry left

The target theorem `AlgebraicGeometry.Scheme.exists_picardCupProductCriterion` is
proved by composition of the two named intermediate results.  Sorry remains in
`picard_dual_directImage_isFiniteLocallyFree` and
`picard_cupProductCriterion_of_finiteLocallyFree`, each with a dedicated node.

## No longer needed

No imports were removed.  The target's former direct proof plan is replaced by the
two explicit intermediate statements.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan requires substantial sheaf-theoretic constructions absent from
the available library, so those constructions are split into the two strict
sublemmas above.

## New nodes

`new-picard-dual-direct-image-finite-locally-free` records the local finite-free
argument for the direct image of the dual.

`new-picard-cup-product-equivalence` records the pairing transpose and counit
criterion once finite local freeness is available.

## Earlier second reading (a previous round; superseded)

A second worker should check that the two intermediate statements are strict parts of the target and that the target proof preserves the unit route.

## Second reading by J1

1. Compared the delivered target module with the repository version. The existing theorem statement is byte-for-byte unchanged; only its proof and the auxiliary import differ.
2. Compiled both delivered modules with `lcompile.py --all`; both compile cleanly. The target has no `sorry`; the two named auxiliary theorems retain their documented `sorry`s, with no axioms, unsafe declarations, or hollow definitions introduced.
3. Checked the two split statements against the target and searched the repository for duplicate declarations. Each is a strict subproblem needed by the target, with its own node and source; neither weakens the target or merely restates it.
4. The proof takes the stated two-step route through the dual finite-local-freeness result and the cup-product equivalence. The unit `sk-prop-av-cube` and its route are preserved. No imports were removable.
5. Checked the DAG `proof`, `proof_deps`, `proof_origin`, Lean declaration records, and new-node metadata against the delivered code. They agree; the only remaining holes are the two named auxiliary theorems.

Changed in this reading: added this review record only; no Lean statements or proofs were changed.
