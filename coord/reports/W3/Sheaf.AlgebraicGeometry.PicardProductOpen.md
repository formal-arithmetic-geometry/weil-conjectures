## What changed

Added `Sheaf.AlgebraicGeometry.PicardProductOpenData`, whose named theorem
`picard_product_open_data` states the geometric construction with explicit isomorphism
witnesses. The core theorem now applies this data theorem and packages the witnesses as
`Nonempty`; the final product openness theorem composes the two isomorphisms directly.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.picard_product_open_core` by reducing it to the
strictly stronger explicit-data theorem, and closed
`AlgebraicGeometry.Scheme.picard_product_open` by composing the returned isomorphisms.
The new theorem `AlgebraicGeometry.Scheme.picard_product_open_data` remains a named sorry,
with node `lem-sc-picard-product-open-data`.

## No longer needed

None. All original proof imports remain needed by the data theorem's stated construction.

## Where the brief, the DAG or earlier work was wrong

The original module had no explicit-data intermediate node, so its geometric core could
not be reduced to a compilable composition. The delivery adds that strictly stronger,
data-level intermediate statement.

## New nodes

`lem-sc-picard-product-open-data` records the explicit-isomorphism intermediate theorem
and its source and proof plan.

## Earlier second reading (a previous round; superseded)

A second worker should verify that `picard_product_open_data` is a strictly stronger
explicit-witness form of the core statement, that the core projection and final
composition preserve the original signatures, and that the unit route remains represented.

## Second reading by W3

1. The delivered modules were diffed against the repository. Existing theorem signatures and definitions are unchanged; the only interface addition is the declared split-off explicit-data theorem and its node.
2. Both modules compile with `lcompile.py --all`. The only remaining `sorry` is the named `picard_product_open_data`, and it has a matching DAG node; no forbidden declarations or hollow definitions were introduced.
3. The explicit-data statement is strictly stronger than the core theorem because it exposes actual isomorphism witnesses, while the core and final theorem retain their original statements. Its source, proof plan, and dependencies are recorded in the node.
4. The proof uses the split-off data theorem and composes the two witnesses; the original public imports remain required by the stated geometric construction. No additional pruning was found.
5. The unit route is preserved: the core theorem feeds the final product openness theorem, and the new data theorem records the same Picard-locus construction beneath it.

Changed during second reading: removed the redundant trailing `True` from the explicit-data theorem and synchronized its node statement, and corrected the core pattern match. No existing target statement changed.
