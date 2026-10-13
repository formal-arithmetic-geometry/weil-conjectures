## What changed

Proved `HomologicalComplex₂.finite_strip_cone_filtration_steps` in
`Sheaf.Algebra.Homology.FiniteStripConeFiltration`, without changing any existing
signature, visibility or existing definition. Private proved helpers construct the
finite degreewise tails, prove antitonicity and differential stability, and establish
both endpoint bounds. The second reader replaced the private assembly helper with
`CategoryTheory.Functor.filtration_of_degreewise`, adding its module
`Sheaf.CategoryTheory.DegreewiseFiltration` as a plain proof-only import. Its
hypotheses exactly match the constructed family and impose no quadrant restriction. The actual component calculations use
Mathlib's total differential and mapping-cone formulas.

The steps node now records this proof rather than citing its own parent theorem.
The unit record has no realized statement or step attached to this technical node;
the finite-strip route and the parent theorem's statement are retained.

Read Stacks Tags [012X](https://stacks.math.columbia.edu/tag/012X) (second filtration
formula) and [0133](https://stacks.math.columbia.edu/tag/0133) (augmentation comparison
and second-variable variant). The proof gives the concrete finite-strip cone
refinement already specified in the parent node.

## Proved and sorry left

Closed one of the original two holes:
`HomologicalComplex₂.finite_strip_cone_filtration_steps`
(node `lem-sc-finite-strip-cone-filtration-steps`). This is a direct proof, not a
new decomposition. No holes were added. The proof uses Mathlib, the
sorry-free filtration/subquotient definitions, and the proved degreewise assembly
theorem. In particular it does not call
`finite_strip_cone_filtration` or the graded comparison.

The only remaining sorry is
`HomologicalComplex₂.finite_strip_cone_filtration_graded`
(node `lem-sc-finite-strip-cone-filtration-graded`), left unchanged. The already
proved `finite_strip_cone_filtration` still combines the two statements.

The construction proof covers the empty strip `r = 0`, arbitrary negative total
and filtration degrees, cutoff `n−r`, and cutoff `n+2`. Outside the strip, all
row degrees are zero by evaluation, so no finite coproduct existence beyond the
supplied `HasTotal` is assumed. The row maps `f` and `hf` are unnecessary for
constructing the filtration, but their original binders are preserved.

Validation: repeated single-file lcompile.py runs; the final module compiles
without warnings. The delivery dry run supplies the declaration/axiom probe.

## No longer needed

No imports were removed: every existing public import is needed by the original
statements or their definitions. No modules or globally reached nodes are pruned.
For the construction steps node alone, the circular proof dependency on
`lem-sc-finite-strip-cone-filtration` is removed. Neither the graded comparison nor
`lem-pur-quasi-iso-cone-acyclic` is needed to construct the filtration.

The first-quadrant cone projection, quotient and graded-isomorphism modules are
not imported: their nonnegative-index hypotheses do not apply to this arbitrary
integer-indexed finite strip. The duplicated private degreewise assembly proof is removed; the public theorem
in `Sheaf.CategoryTheory.DegreewiseFiltration` is used instead.

## Where the brief, the DAG or earlier work was wrong

Both decomposed nodes originally cite `lem-sc-finite-strip-cone-filtration`, whose
Lean proof invokes those same nodes, giving circular proof plans. The construction
node is repaired here. The unchanged graded node still needs a noncircular plan
for its objectwise quotient and differential comparison; its current proof text
also describes filtration construction rather than graded comparison.

Searches run through msearch.py: LeanFinder on differential-stable degreewise
subobjects and on associated graded rows of a double complex; Loogle on
`"Subobject", "HomologicalComplex"` and `"cokernel", "Subobject"`; grep on
`finite_strip_cone|subcomplex_of`. No exact reusable comparison was found. Direct
rg reads found the proved degreewise construction used above and the
first-quadrant comparisons. `DoubleComplexTotal.secondFiltration_graded` also
assumes first-quadrant support and gives an objectwise filtration of the total,
not the supplied subcomplex filtration of an augmentation cone. It therefore
cannot be applied directly to close the remaining hole.

## Second reading by F1

1. Compared the complete module against the repository version with `diff`.
   All three existing public theorem signatures, their visibility, docstrings,
   and the original public imports are byte for byte unchanged. No existing
   definition was changed, no hypothesis added, and no conclusion weakened.
   The only new definition is the private explicit finite image-supremum
   `stripStep`; its data contains no hole. Verdict: pass.

2. Read each helper and the construction proof. Antitonicity removes generators;
   differential stability follows from the two total differential components and
   the two source cone components. The augmentation term uses exactly `hb`.
   The top proof tests all coprojections, using `hsupport` outside the strip;
   the bottom proof uses nonnegative supported horizontal indices. The assembly
   theorem factors differentials through monomorphisms and proves square-zero by
   cancellation. Compiled the repaired module with lcompile.py, without errors
   or warnings. In a scratch copy, `#print axioms` for the construction and public
   assembly theorem returned only `propext`, `Classical.choice`, and `Quot.sound`.
   The graded theorem and parent returned those plus `sorryAx`, as expected.
   There is exactly one remaining `sorry`, in the named original graded theorem;
   no new holes or forbidden declarations were introduced. Verdict: pass.

3. No statements were split off and no nodes were added. The remaining graded
   theorem and its existing docstring and node are unchanged. Tested the new
   private constructions conceptually at `r = 0`, `r = 1`, negative `n` and `p`,
   and both endpoint cutoffs: the empty strip has zero total, and source degree
   `n+1` is included at `n-r` and excluded at `n+2`. These arguments do not require
   a first-quadrant bound or any coproduct beyond the supplied `HasTotal`.
   Independent msearch LeanFinder and Loogle queries for stable subobjects and
   factorization returned building blocks, not the finite-strip comparison.
   Direct rg searches of Sheaf and the upstream sources found the exact public
   assembly theorem in `Sheaf.CategoryTheory.DegreewiseFiltration`. Replaced the
   duplicated private assembly helper with that theorem. Verdict: pass after repair.

4. All original public imports occur in the original statements or their
   definitions: integer intervals, total, single complex, mapping cone, and
   filtered subquotients. The sole added import is plain `import`, because only
   the proof uses it. No existing modules are pruned. The old steps-node dependency
   on its parent is completely listed under `No longer needed`; the construction
   does not use the graded comparison. Read `dag/units/sk-thm-picard-duality.json`:
   its `realized.statement` and its step realization are empty, so this technical
   construction bypasses no recorded unit realization. The parent and row-cone
   comparison remain in place. Verdict: pass.

5. Compared the delivered node JSON against the repository version: only `proof`,
   `proof_deps`, and `proof_origin` change. The statement and Lean signature are
   unchanged. The proof now records finite-tail stability, the public assembly
   theorem, and endpoint bounds; `proof_deps` is exactly the union of step uses.
   The assembly node is an existing, proved general-purpose tool from another
   unit, used with identical hypotheses; no unit route is replaced. Its source
   module has no sorry and its axiom probe is clean. The pre-existing circular
   plan of the untouched graded node is reported above for its future worker.
   Verdict: pass for the delivered node; the unchanged graded plan remains open.

Second-reading changes: removed the duplicated private `filtration_of_degreewise`
proof (54 lines), added the proof-only import of `DegreewiseFiltration`, qualified
its use, and updated the construction node and report to record this reuse. Closed
one original hole and added zero holes: this is a proof, not a decomposition.
