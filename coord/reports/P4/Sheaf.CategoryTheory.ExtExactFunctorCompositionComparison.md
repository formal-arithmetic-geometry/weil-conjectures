## What changed

The duplicate proof is exposed under the canonical name
`CategoryTheory.Abelian.Ext.mapExactFunctor_comp_mk₀_eq`, with the complete derived-category
proof retained. A compatibility theorem with the former name remains so existing callers
continue to compile while downstream re-pointing can land independently.

## Proved and sorry left

No sorry remains in the delivered module. The canonical theorem and compatibility theorem
compile with only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No additional imports or proof dependencies are needed. The canonical declaration supersedes
new uses of `exactFunctorCompositionComparison`.

## Where the brief, the DAG or earlier work was wrong

The upstream review identifies the old theorem as a duplicate of the canonical Mathlib
lemma, but that lemma is absent from this checkout. The complete proof is therefore retained
locally under the canonical name. A compatibility theorem is kept because the eight callers
are held outside this repair sandbox; removing it would make the global library fail until
those callers are delivered together.

## Earlier second reading (a previous round; superseded)

Pending second reader. Change record: `coord/changes/ext-composition-canonical-name.md`.

## Second reading by P4

1. Compared the delivered module with the repository version. The existing private helper
   is unchanged; the original theorem's elaborated signature is unchanged (the compatibility
   alias has only an extra definitionally irrelevant pair of parentheses), while the reported
   interface change is the canonical theorem name.
   Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or `sorry`. The proof
   uses only the permitted classical axioms (as recorded in the scratch axiom check), and
   no forbidden declarations or hollow definitions were added. Verdict: pass.
3. Checked the canonical theorem and alias against the node statement. Both have exactly the
   stated hypotheses and conclusion, and the canonical theorem is proved by the complete
   derived-category naturality argument. No split-off statements were added. Verdict: pass.
4. Reviewed the proof route and imports. The route follows the unit's derived-category
   comparison and shifted naturality steps; `Mathlib.Algebra.Homology.DerivedCategory.Ext.Map`
   and the exact-functor shift module are used, with no removable imports found. Verdict: pass.
5. Checked the DAG node and change record: the node points to
   `mapExactFunctor_comp_mk₀_eq`, its proof dependencies match the implementation, and the
   canonical-name change is documented with affected callers. Verdict: pass.

Changed during this second reading: removed an unnecessary parenthesization change to the
private helper, and added this review record. No proof or statement content was otherwise
changed.
