## What changed

Replaced the target proof with a complete composition of two strictly simpler interfaces: one constructs transitions satisfying the projection equations, and one proves the cocycle from those equations. Added the two corresponding statement modules.

## Proved and sorry left

The target theorem `exists_arrow_product_transitions_cocycle` is proved by applying the two intermediate interfaces. The intermediate declarations `exists_arrow_product_transitions` and `arrow_product_transitions_cocycle_of_projections` remain as named sorries, respectively covering product-preservation construction and the projection-wise cocycle calculation.

## No longer needed

No imports or planned dependencies were removed; the proof uses only the product and continuous-site imports already present, plus the two new interfaces.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan requires a lengthy universal-property construction and projection-wise comparison calculation. These are represented as two strict intermediate statements so the target composition is checked in Lean.

## New nodes

`lem-weil-pbc-arrow-product-transitions-existence` for `exists_arrow_product_transitions`.
`lem-weil-pbc-arrow-product-transitions-cocycle-law` for `arrow_product_transitions_cocycle_of_projections`.

## Earlier second reading (a previous round; superseded)

Pending second reading.

## Second reading by G2

1. Compared the delivered target module with the repository version. The target
   declaration and all existing signatures are unchanged; only its proof and the
   two explicitly new modules are present.
2. Compiled all three modules with `lcompile.py --all`; they compile without errors.
   The two new interface theorems intentionally remain named `sorry`s and have
   corresponding DAG nodes; the target theorem has no `sorry`.
3. Checked the intermediate statements against their Lean declarations and the
   edge cases of empty products. They are strictly weaker than the target and
   introduce no altered definitions or hypotheses.
4. The target proof follows the stated route: obtain projection equations from
   `exists_arrow_product_transitions`, then apply the projection cocycle lemma.
   No imports were removable.
5. The unit route is retained: the target still uses the projection construction
   and projection-wise cocycle interfaces. I corrected both new DAG node
   statements to match their Lean declarations exactly and added this review.

Changed the two new node statements and their proof descriptions to distinguish
the existence interface from the separate cocycle implication.
