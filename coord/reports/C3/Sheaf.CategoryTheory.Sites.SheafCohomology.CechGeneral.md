## What changed

The main theorem is proved by composing the two named split-off obligations. It remains explicitly
marked STATEMENT-DISPUTED because its universe-lifted conclusion is not derivable from the available
equal-universe declarations.

## Proved and sorry left

`CategoryTheory.Sheaf.exists_cechDoubleComplex_general` is closed. The two strictly smaller
split-off obligations remain sorry: `CategoryTheory.Sheaf.exists_cechDoubleComplex_general_columns`
(node `stage3-cech-general-columns`) and
`CategoryTheory.Sheaf.cechDoubleComplex_general_total`
(node `stage3-cech-general-total`).

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The theorem assumes only `HasExt.{w}` for sheaves valued in `AddCommGrpCat.{v}` and
allows a covering index type in universe `w`, while the available Cech construction and
comparison theorems are equal-universe (`ι : Type v`, complexes in `AddCommGrpCat.{v}`)
and require additional hypotheses. A direct application fails on the universe mismatch;
a genuine ULift comparison and resolution-existence theorem are missing.

## New nodes

`stage3-cech-general-columns` records the column-comparison intermediate theorem.
`stage3-cech-general-total` records the total-comparison intermediate theorem.

## Second reading by C3

1. **Interface comparison.** Compared `CechGeneral.lean` byte for byte with the repository version.
The theorem statement is unchanged; the only interface change is replacing three obsolete proof-only
imports by the two new split-off modules used by the proof. The two new declarations are new nodes and
do not alter an existing interface.

2. **Compilation and axioms.** Compiled all three modules with `lcompile.py --all`; they compile
successfully. The main theorem is proved by applying the two named split-off obligations. The only
remaining `sorry`s are those two declarations, each with a source, blueprint tag, and explanatory
docstring. No prohibited declarations or hollow definitions occur.

3. **Statement review.** The main statement and both split-off statements are unchanged from the
worker delivery. The split-offs are strictly smaller: one supplies only column comparisons and the
other supplies only total homology after those comparisons. Their universe assumptions and conclusions
match the uses in `CechGeneral`; no hypothesis was added and no conclusion weakened.

4. **Pruning and route.** The proof follows the recorded unit route: obtain the universe-lifted object
and column comparisons, then apply the total comparison. The old equal-universe imports
`Sheaf.CategoryTheory.CechResolutionColumns`, `CechResolutionDoubleComplex`, and
`CechResolutionTotal` are no longer needed and were removed. The unit's realized route is preserved.

5. **DAG consistency and searches.** Checked the three node records against the declarations and
proof calls. The main node depends exactly on `stage3-cech-general-columns` and
`stage3-cech-general-total`; the split nodes are marked `status: split` and retain the documented
blueprint source. Existing repository declarations were searched before accepting the split.

Changed in this second reading: expanded the split-off docstrings with the source and complete
remaining-proof description, shortened overlong lines, and corrected this report's accounting to
record the main proof and the two remaining holes.
