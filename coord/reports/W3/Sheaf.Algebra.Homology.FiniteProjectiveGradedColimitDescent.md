## What changed

Completed the proof body of
`ModuleCat.exists_finite_projective_graded_model_of_directed_colimit` in
`Sheaf.Algebra.Homology.FiniteProjectiveGradedColimitDescent`, keeping its signature and
visibility unchanged. The proof obtains single-term models, bounds their finitely many stages,
extends them to one common stage, and uses the actual zero module outside `Finset.Icc a b`.
Private proved helpers establish scalar-extension finiteness and projectivity, finite-set
upper bounds in a directed preorder, and the canonical iterated-base-change isomorphism.

Added the proof import `Sheaf.Algebra.Homology.FiniteProjectiveModuleColimitDescent` and the
Mathlib proof imports `Mathlib.RingTheory.TensorProduct.Finite` and
`Mathlib.Data.Int.Interval`. The new module states single-module descent, grouping steps 1–3
of the original plan. Its docstring and node give the complete finite-presentation and splitting
argument, including reduction from a preorder to its antisymmetrization. Updated the original
node's proof, dependencies and origin to match the Lean assembly. No definitions or existing
statements changed. All witness choices are local to an existential theorem proof.

## Proved and sorry left

Closed the original hole in
`ModuleCat.exists_finite_projective_graded_model_of_directed_colimit`
(node `lem-pc-finite-projective-graded-colimit-descent`). No sorry remains in the assigned module.

Added one hole:
`ModuleCat.exists_finite_projective_module_model_of_directed_colimit`
(node `lem-pc-finite-projective-module-colimit-descent`), whose whole proof is `:= by sorry`.
This is a decomposition, not a net hole reduction: one hole closed and one added. The remaining
statement concerns one module only; it has no grading, bounds, simultaneous stage, or zero-support
claim. The Lean assembly of these additional claims is complete. The existing dependency
`ModuleCat.finitePresentation_descent_directedColimit` remains unmodified and still has sorry.

Both sandbox modules compile without warnings using `lcompile.py --all`. The assembly handles
`b < a` through the empty finite set, and uses only directedness, never antisymmetry. The new
single-term statement was checked against zero modules, singleton diagrams and directed
preorders with equivalent indices: these require no additional hypotheses. The final dry run
checks all delivered declarations with the project's axiom probe.

## No longer needed

Removed the assigned module's direct proof import
`Sheaf.Algebra.FinitePresentationColimit`, since it now only appears in the plan of the
single-module lemma, whose module imports it. This is relocation, not transitive pruning:
`lem-pc-fp-module-map-descent-affine` is still required below the new node. The projective-module
Mathlib leaf remains required by the public statement and the tensor-product instance.
The old proof dependency `def-weil-pbc-projective-module` is also removed from the graded
node's direct `proof_deps`; it remains a statement dependency there and a proof dependency
of the new single-module node. Both old proof dependencies are thus accounted for, and neither
is transitively pruned. No existing DAG node or library module is pruned.
All existing public imports are retained.
An initially added explicit zero-preservation import was unnecessary and was removed after a
successful compile without it.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The finite-presentation theorem is stated for partial orders,
whereas this item accepts preorders; the new remaining lemma explicitly retains the original
plan's antisymmetrization and colimit transport step. The unit's route is unchanged.
The cited Stacks TeX files and blueprint section text are not present in this local checkout;
the existing DAG plan was read and Stacks Tags 0BC7 and 05N7 were checked on the official site:
https://stacks.math.columbia.edu/tag/0BC7 and https://stacks.math.columbia.edu/tag/05N7.
LeanSearch returned Internal Server Error; that search is recorded as unavailable, alongside
successful LeanFinder, Loogle and source searches.

## New nodes

`lem-pc-finite-projective-module-colimit-descent`, in
`dag/nodes/sec-picard-framework/lem-pc-finite-projective-module-colimit-descent.json`, corresponds
to the new module `Sheaf.Algebra.Homology.FiniteProjectiveModuleColimitDescent` and declaration
`ModuleCat.exists_finite_projective_module_model_of_directed_colimit`. It is strictly the
single-term part of the original plan; the finite simultaneous-stage and bounded-support
argument has been proved in Lean in the assigned module. No change records or forced
adaptations are needed.

## Second reading by W3

1. **Interfaces: PASS.** Compared the delivered graded module with the repository by `diff`
   and checked its existing theorem signature as an exact byte string: unchanged. The only
   additions are private proved helpers, proof imports, the proof body, and one new theorem
   module. Compared the existing node JSON: only `proof`, `proof_deps`, and `proof_origin`
   differ. No definitions or existing public declarations changed; no change record is needed.
2. **Kernel and holes: PASS as a decomposition.** Independently ran `lcompile.py --all`:
   both modules compile cleanly. Scanned both sources: the only hole is the new public named
   single-module theorem, with whole proof `:= by sorry`; there are no forbidden declarations
   or hollow definitions. In a scratch copy, `#print axioms` for all four private helpers shows
   only `propext`, `Classical.choice`, `Quot.sound`. The graded theorem and remaining
   single-module theorem additionally show `sorryAx`, as reported. The private isomorphism
   definition constructs its data from `extendScalarsComp`, the cocone identity, and `eqToIso`;
   it uses no unproved existence theorem. Model choices occur only inside the existential
   theorem proof, and no chosen witness becomes a library definition.
3. **Split statement: PASS.** Read the full single-module signature, its proof docstring,
   its node, and the existing finite-presentation object/map/equality theorem. The splitting
   argument is valid: finite projectivity gives finite presentation and a finite free retract;
   descend the two maps and then their composite identity, obtaining a projective stage model.
   The canonical base-change maps are fixed on generators by the existing map-descent clause.
   Antisymmetrization preserves directedness and transports the diagram via a thin-category
   equivalence. Checked zero modules, singleton diagrams, the zero ring, and mutually comparable
   equivalent indices; no missing hypothesis was found. This is strictly the single-term part
   of the graded argument, not a renamed graded conclusion: finite simultaneous-stage assembly
   and zero support are proved in Lean. Independently checked the sources at
   https://stacks.math.columbia.edu/tag/0BC7,
   https://stacks.math.columbia.edu/tag/05N7, and
   https://stacks.math.columbia.edu/tag/00NX. Repeated searches with different queries:
   LeanFinder "finite rank direct summand descends along filtered colimit rings" finds only
   fixed-ring module colimits and ring finite-presentation results; Loogle
   "Module.Projective, CommRingCat" gives no hits. Source searches across both library roots
   and Mathlib for descent/colimit/direct-limit and projective/finite-presentation found no
   replacement for this theorem. Closing it requires the substantial map/equality transport
   argument, not a short application of an existing proved declaration.
4. **Route and pruning: PASS.** Read the graded assembly top down. Scalar-extension
   finiteness and projectivity use Mathlib instances; iterated base change uses Mathlib's
   canonical comparison; the finite common stage uses directedness. The empty interval case
   follows from the empty finset case and concrete zero modules. New imports are proof-only;
   interval and tensor finiteness imports supply precisely the assembly's facts/instances.
   The finite-presentation proof import has moved to the single-module module. Both old direct
   proof dependencies remain transitively needed and are now explicitly accounted for above.
   No module is pruned. Read `dag/units/sk-thm-picard-semicon.json`: its `realized` fields are
   unchanged, and the term-descent refinement keeps the existing route.
5. **DAG: PASS.** The graded node's three steps describe single-term descent, common-stage
   scalar extension, and zero support exactly as implemented; its `proof_deps` is their union.
   The new node retains the original finite-presentation and projectivity dependencies, has
   its source, complete proof plan, searches, creation/blueprint/chapter/unit records, and Lean
   attachment. Its mathematical statement matches its Lean signature and the remaining hole.

Second-reading changes: clarified the accounting of both old direct proof dependencies in
`## No longer needed` and appended this independent review. No Lean repair was necessary.
One original hole is closed and one strictly simpler hole is added: net zero, a decomposition.
