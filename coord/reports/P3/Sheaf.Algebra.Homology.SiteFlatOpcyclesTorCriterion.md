## What changed

Proved `SheafOfModules.isFlat_opcycles_of_universal_tensor_exactAt` in
`Sheaf.Algebra.Homology.SiteFlatOpcyclesTorCriterion`, preserving its entire signature
and public imports. Added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` and retained `TensorClosed`.
No definitions, statements, visibility, or other modules changed.

The source library already proves the generic criterion
`CategoryTheory.ObjectProperty.flat_opcycles_of_exactAt`. Its hypotheses use
categorical flatness and termwise tensorRight. The proof converts sheaf flatness to
categorical flatness using symmetry and the closed-category flatness criterion.
`mapBifunctorSingle₁Iso` followed by the prolonged braiding identifies the given total
tensor with termwise tensorRight; `ExactAt.of_iso` transports exactness. Applying the
generic criterion and taking its second conjunct proves the original conclusion.

Updated the item's DAG `proof`, `proof_deps`, and `proof_origin` to record these
comparisons and the proved upstream criterion. This is below the unit level:
`dag/units/sk-thm-properbasechange.json` does not list this node as a unit statement or
step, and its required statement and all unit steps remain unchanged.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.isFlat_opcycles_of_universal_tensor_exactAt`
(node `lem-weil-pbc-site-flat-opcycles-tor-criterion`).
Added zero holes and split off zero statements. No `sorry` remains in the delivery.

The proof compiled cleanly after the four unused imports were removed. An explicit
`#print axioms SheafOfModules.isFlat_opcycles_of_universal_tensor_exactAt` reported
exactly `[propext, Classical.choice, Quot.sound]`, so the result has no transitive
sorry dependency. The diagnostic command was removed from the delivered source.
The import-direction check permits the new import. The proof needs flatness only in
degrees `n - 1` and `n`; it handles all integers and arbitrary small sites, with no
boundedness, enough-points, nonzero-ring, or global lifting assumption.

## No longer needed

Removed these proof-only imports:

- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Mathlib.CategoryTheory.Sites.EpiMono`
- `Mathlib.Algebra.Homology.ExactSequence`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`

Removed these nodes from this item's proof dependencies:

- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`
- `def-weil-pbc-exact-sequence`
- `def-sp-abelian`

The generic abelian refinement proof supplies the cokernel argument directly, so
this item needs no sheaf-section lifting infrastructure. `FlatOnSite` is unnecessary
for the unchanged specialized `IsFlat` signature, whose definition is already in
its retained public import `Flat`. Other parents may still need these modules and
nodes; these are dependencies pruned from this item, not a claim that they are
absent from the entire targets' closure. All original public imports are retained.
No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The node's `lean_candidates` had already identified the generic upstream criterion,
but recorded the missing flatness and tensor-model comparisons as preventing its
use. Both comparisons are now proved by existing APIs; the longer sectionwise
chase is unnecessary. The original mathematical statement and planned argument are
valid. No interface repair, forced adaptation, or new node is needed.

Searches actually run through `msearch.py`: LeanFinder for universal tensor exactness
and flat opcycles returned eight module-flatness results; Loogle for `"flat",
"opcycles"` and grep for `flat.*opcycles|opcycles.*flat` returned zero Mathlib hits.
Repository `rg` found the proved generic criterion and existing uses of the same
flatness conversion in `AffineLiftEventualFreeKernels`. Read its entire generic
criterion proof, `BifunctorSingle`, `TensorClosed`, and the flatness definitions.
The independent reader should check the new DAG proof against these exact APIs.

## Second reading by P3

1. **Interface: PASS.** Compared the sole delivered Lean module with the shared
   repository using `diff -u` and the project's declaration parser. The complete
   statement, binders, visibility, and docstring of
   `SheafOfModules.isFlat_opcycles_of_universal_tensor_exactAt` are unchanged;
   there are no added declarations or definitions. The only Lean changes are its
   proof and proof-only imports. No change record or forced adaptation is needed.
2. **Proof and trust: PASS.** Independently compiled the delivered file with
   `lcompile.py` (20.2 seconds, no errors or warnings). Compiled a scratch copy
   with `#print axioms` (17.1 seconds): exactly `propext`, `Classical.choice`, and
   `Quot.sound`, with no `sorryAx`. The delivered source contains no `sorry` or
   forbidden declaration mechanism. Read `tensorClosed`, the definition of
   `IsFlat`, `ObjectProperty.flat`, `flat_iff_preservesFiniteLimits`,
   `mapBifunctorSingle₁Iso`, and the entire generic flat-opcycles criterion.
   The local structures use the original monoidal tensor; choices are from the
   already proved `tensorClosed` compatibility package, not an unproved existence
   theorem. The first braiding transports right-tensor left exactness to
   left-tensor left exactness. The second braiding acts on complexes after the
   degree-zero single-complex isomorphism, preserving the degree `n - 1`.
   The criterion uses precisely flatness in degrees `n - 1` and `n`, and its
   second conjunct is the unchanged sheaf-flatness conclusion.
3. **Splits and edge cases: PASS.** Zero new statements, nodes, or holes. Thus no
   lower theorem merely renames the goal. Checked the zero complex, the zero
   coefficient ring, arbitrary negative degrees, and a complex concentrated in
   degree `n`: the argument imposes no extra nonzero, boundedness, or enough-points
   assumption. In the last case the opcycle is the already flat degree-`n` term.
   The source [Stacks Tag 08G0](https://stacks.math.columbia.edu/tag/08G0) uses
   universal middle exactness of the same three tensor terms. The present
   generalization assumes that exactness directly; the proved upstream criterion
   supplies the full abelian diagram chase without the source's boundedness or
   Tor-amplitude assumptions.
4. **Route and pruning: PASS.** Searched independently through `msearch.py` with
   `grep 'flat.*cokernel|exact.*opcycles|opcycles.*exact'` (25 Mathlib hits, none a
   shorter flatness criterion), and searched the repository for the tensor and
   opcycle comparisons. The proof already takes the direct upstream route.
   Both proof-only imports are used: `TensorClosed` supplies compatibility
   structures and `FlatModel` the generic criterion and tensor comparison.
   Public imports provide the unchanged statement's sheaf/complex definitions
   and instances. The four removed imports and all four old proof dependencies
   absent from the new proof are listed under `## No longer needed`.
   Read `dag/units/sk-thm-properbasechange.json`: this auxiliary node occurs in
   neither its realized statement nor its realized steps; no unit route is
   bypassed or changed.
5. **DAG agreement: PASS.** Compared the node JSON with the repository. Only
   `proof`, `proof_deps`, and `proof_origin` differ. Their four steps follow the
   actual local structures, flatness conversion, complex isomorphism, and
   upstream criterion application. The union of step `uses` equals
   `proof_deps`; the recorded Lean statement matches the delivered declaration.
   The proof origin names the exact proved generic declaration and its file.
   There are no new-node fields to audit.

Second reading changed only this report by appending the independent review.
The Lean proof and node passed unchanged. Holes closed: the one declaration named
above. Holes added: none. Split off: none.
