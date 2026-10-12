## What changed

Proved `CategoryTheory.InjectiveResolution.exists_horseshoe_prescribed_rows` with its
signature unchanged. Added the proved private helper `exists_twisting` and the proof-only
import `Mathlib.CategoryTheory.Abelian.Refinements`.

The proof chooses off-diagonal differential entries by injectivity and exactness, assembles
the triangular biproduct complex and its augmentation, and proves degree-zero exactness
by a diagram chase using epimorphic refinements. The DAG proof now records this route.
The unit has no realized steps assigned to this construction, so no unit route is bypassed.

## Proved and sorry left

Proved `CategoryTheory.InjectiveResolution.exists_horseshoe_prescribed_rows`
(node `lem-sp-horseshoe-prescribed-row-construction`) and private helper `exists_twisting`.
No `sorry` remains and none is added. No new module or statement dependency is introduced.
Local single-file compilation passes without warnings; the delivery dry run performs the
axiom probe and server checks.

## No longer needed

`lem-weil-pbc-snake-lemma-abelian` is removed from this node's proof dependencies.
Its Mathlib declaration `CategoryTheory.ShortComplex.SnakeInput.snake_lemma` and module
`Mathlib.Algebra.Homology.ShortComplex.SnakeLemma` are not needed by this proof.
There were no proof-only imports in the original module to remove. No Sheaf dependency
module is needed: all supporting facts are proved Mathlib declarations. The repeated
cokernel-sequence construction in the old plan is unnecessary.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The old proof plan and unchanged theorem docstring describe
one possible cokernel/snake argument; this delivery instead proves the same statement by
triangular differentials. Its actual route is documented in the node and proof comments.
The initial twisting equation and each recursive square-zero equation are checked by Lean;
the proof works for zero objects and split sequences without additional assumptions, and
does not assume EnoughInjectives for the category.

## Second reading by T2

1. Compared the delivered module with the repository version. The public theorem signature is byte-for-byte unchanged; only its proof and a proof-only import were added. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no warnings. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `sorryAx`. Explicit `#print axioms` probes in a scratch copy show exactly `propext`, `Classical.choice`, and `Quot.sound` for both the public theorem and private helper. Verdict: pass.
3. The private helper `exists_twisting` is proved, not split off, and introduces no public statement. The theorem statement is unchanged and its edge cases (zero and split rows) are covered by the biproduct construction. Verdict: pass.
4. The triangular differential route is below the unit level and preserves the unit's realized route; the removed snake-lemma dependency is recorded in the node and report. The added `Refinements` import is proof-only and necessary. Independent LeanFinder and Mathlib searches for upper triangular differentials and off-diagonal extensions found resolution comparison constructions (`descFOne`, `descFSucc`), which do not directly provide these shifted twisting maps or the prescribed augmentation. Searching the project found only the downstream prescribed-resolution theorem, which already depends on this item. No shorter applicable route was found. Verdict: pass.
5. The DAG proof, proof dependencies, and proof origin match the Lean proof; no new nodes or statement changes are present. Verdict: pass.

Changed the report by recording this second reading. No Lean repair was necessary.
