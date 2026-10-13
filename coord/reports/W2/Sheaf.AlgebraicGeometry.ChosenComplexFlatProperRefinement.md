## What changed

Proved `AlgebraicGeometry.exists_chosen_complex_flat_proper_refinement` from one
strictly simpler, single-module eventual descent theorem. Its existing signature and
visibility are unchanged. The complex K is constructed by the additive tensor-pullback
functor on complexes, rather than selected from an existence statement. A proved private
helper treats zero modules using flat sections and an empty proper support. The main
proof chooses the common stage by finite-set induction and proves the differential
equation by naturality of the inverse tensor-pullback composition isomorphism.

Added `Sheaf.AlgebraicGeometry.ChosenModuleFlatProperStage` as the single-module
interface glue for the existing flatness, proper-support, preservation and final-poset
lemmas. Updated the main node's proof route to match the Lean. No definitions,
existing statements, public imports, or other held modules were changed.

Both modules compile locally in import order with no warnings. The empty interval,
zero terms, empty source and empty support are covered. Preorders are handled by the
new module's sourced proof plan; antisymmetry is not added to the main statement.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.exists_chosen_complex_flat_proper_refinement`
(node `lem-pc-chosen-complex-flat-proper-refinement`). No sorry remains in the item.

Added one named hole:
`AlgebraicGeometry.exists_eventually_chosen_module_flat_proper`
(node `lem-pc-chosen-module-flat-proper-stage`), in the new module. This is a
single fixed module with eventual flatness and proper support, without a complex,
differentials, a boundedness claim, a chosen replacement, or a comparison equation.
Its docstring and node give the full proof plan and sources.

This is a decomposition: one upper hole closed, one lower hole added, net zero.
The private helper `zero_flat_proper` and the entire assembly proof are proved.

## No longer needed

Removed direct imports from the item:
- `Mathlib.CategoryTheory.Presentable.Directed`;
- `Sheaf.AlgebraicGeometry.FlatModuleDescent`;
- `Sheaf.AlgebraicGeometry.ProperSupportDescent`;
- `Sheaf.AlgebraicGeometry.TensorPullbackFlatProperSupport`.

The corresponding nodes `lem-weil-pbc-filtered-category-exists-directed-final`,
`lem-pc-flat-module-descent`, `lem-pc-proper-support-descent`, and
`lem-pc-tensor-pullback-flat-proper-support` are no longer direct proof dependencies
of the complex assembly, but all remain needed below the new single-module theorem.
No module is claimed to leave the targets' transitive import closure. Base change,
tensor pullback and its identity/composition nodes remain used. The unit route is kept.

## Where the brief, the DAG or earlier work was wrong

The stated FlatModuleDescent theorem takes a PartialOrder and a module at its starting
stage with ordinary pullback, whereas this item takes a Preorder and a module already
chosen at a later base-changed stage. ProperSupportDescent uses ordinary pullback too.
The plan's pullback-pasting and final-poset sentences therefore need nontrivial
interface glue; they are precisely the single-module hole, not an obstruction to
proving the finite-complex assembly. No statement was found false.

The local literature checkout has the tracked lists but not the Stacks text files.
The primary Stacks pages for 05LY, 081G, 0032 and 0CYS were read online. The helper
follows the existing DAG's same cited argument, with a full explanation that an
arbitrary later stage need not be in the final functor's image. LeanSearch returned
HTTP 500, recorded as unavailable, not as evidence of absence.

## New nodes

`lem-pc-chosen-module-flat-proper-stage`, in
`dag/nodes/sec-picard-framework/lem-pc-chosen-module-flat-proper-stage.json`, states
and sources the one-module eventual flatness/proper-support interface. Its Lean is
`Sheaf.AlgebraicGeometry.ChosenModuleFlatProperStage`; its only theorem is named
`AlgebraicGeometry.exists_eventually_chosen_module_flat_proper`. No change record is
needed: all existing signatures, definitions and visibility are unchanged.

## Second reading by W2

1. Compared both delivered modules with repository versions. Existing declarations keep byte-for-byte signatures; only the documented new theorem is added. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`; no errors or warnings. The complex theorem has no sorry; the sole remaining sorry is the named split-off theorem, with source, proof plan, and DAG node. Verdict: pass.
3. Checked the split-off statement and edge cases (zero terms, empty interval, empty support). It is strictly simpler than the target and chooses no arbitrary data. Verdict: pass.
4. Checked the proof route and imports: finite-stage assembly, additive tensor pullback, zero-term support, and pullback naturality are used; removed imports and dependencies are recorded above. Verdict: pass.
5. Checked DAG proof/proof_deps and unit realization against the Lean route; the unit route is preserved and the new node records its declaration and source. Verdict: pass.

Second-reading changes: appended this review and its verification details only; no Lean or
node repair was needed. Independently searched with leanfinder for “eventual flatness and
proper closed support of a fixed finitely presented sheaf under inverse limits of affine
Noetherian schemes”, and with rg for chosen-module, eventual-flatness and proper-support
names. Results included affine-limit section descent and scheme-flatness criteria, but no
exact theorem. Read FlatModuleDescent, ProperSupportDescent and
TensorPullbackFlatProperSupport: the fixed-stage pullback/pasting and preorder interface
remain nontrivial, so the single-module hole cannot be closed in a few minutes.

A scratch copy compiled with #print axioms for both public theorems: each uses only
propext, Classical.choice, Quot.sound and sorryAx. The unit's realized.statement and
realized.steps entries are empty; this delivery does not alter them or bypass a recorded
realization. Checked Stacks 05LY, 081G and 0032 directly against the new proof plan.
The final directed-poset argument must restrict to a tail above an object mapping above j;
that tail remains final, giving exactly the displayed chosen-module situation.
Dry run printed OK, with review class CODEX (new node, module and split-off hole).
