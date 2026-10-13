## What changed

Replaced the hole in `AlgebraicGeometry.finite_flat_proper_support_descent` without
changing its signature or any public imports. The proof first invokes existing
`exists_finitelyPresented_complex_of_limit`, transports flatness and proper support
across the resulting isomorphisms using two proved private helpers, refines the chosen
finite-stage complex, and composes both families of isomorphisms. The differential
equation is proved by associativity and the two input compatibility equations.

Added `Sheaf.AlgebraicGeometry.ChosenComplexFlatProperRefinement`, with one strictly
intermediate statement about a complex already given at a finite stage. It does not
descend arbitrary limit complex data. Updated the item's DAG proof and dependencies.
All files compile together using lcompile.py. No definitions or target signatures changed.

## Proved and sorry left

Closed original hole: `AlgebraicGeometry.finite_flat_proper_support_descent`
(node `lem-pc-finite-flat-proper-support-descent`). No sorry remains in the item's module.
The private helpers `flatOver_of_iso` and `supportProper_of_iso` are completely proved.

Added one hole: `AlgebraicGeometry.exists_chosen_complex_flat_proper_refinement`
(node `lem-pc-chosen-complex-flat-proper-refinement`). Its complete source-based proof
in words is in its docstring and node. This is a decomposition: one upper hole closed,
one new lower hole added, net zero. The existing imported finite-presentation complex
descent theorem is still sorry; this delivery neither adds nor closes its hole.

## No longer needed

Removed direct proof imports `Sheaf.AlgebraicGeometry.FlatBoundedComplexDescent`
and `Sheaf.AlgebraicGeometry.ProperSupportDescent`. The item's direct DAG dependencies
are now `lem-pc-fp-complex-descent` and `lem-pc-chosen-complex-flat-proper-refinement`.
The combined `lem-pc-flat-bounded-complex-descent` is unnecessary for this route,
and its module can be pruned wherever it has no other users. Its prerequisites
`lem-pc-flat-module-descent` and `lem-pc-fp-complex-descent` remain mathematically needed.
`lem-pc-proper-support-descent` is still needed by the refinement node, so it is not
claimed to be globally unnecessary. No other original dependencies are pruned.

## Where the brief, the DAG or earlier work was wrong

The original planned `flat_bounded_complex_descent` and its flat-module dependency
require `[PartialOrder I] [IsDirectedOrder I]`, whereas this item has only a directed
preorder. Antisymmetry cannot be inferred. Existing finite-presentation complex descent
accepts the item's hypotheses, so it supplies the initial chosen complex directly.
The refinement proof records transport through a final directed poset to handle the
flat-module lemma's more restrictive interface. No dependency signatures were changed.

The earlier sandbox contained only the unchanged original sorry and search logs.
The cited local Stacks source files are absent on this machine; the existing cited
Tags 01ZR, 05LY, 081G and 0CYS were read from the official Stacks website.
The unit's realized statement and steps are empty; its route is preserved: descent
of finite complex data, eventual flatness and proper support, then common-stage
base change. Edge cases of the new lemma include empty degree intervals, zero terms,
empty source schemes, and directed preorders with mutually comparable distinct indices.

## New nodes

`lem-pc-chosen-complex-flat-proper-refinement` in
`dag/nodes/sec-picard-framework/lem-pc-chosen-complex-flat-proper-refinement.json`
records common-stage refinement of a fixed finite-stage bounded complex. Its hypotheses
refer only to that complex and its limit pullback, with no input limit complex G or
comparison to G. It handles geometric stage enlargement, while the parent supplies
the initial model and proves the final isomorphism and differential compatibility.
Blueprint search for bounded complex flat proper support found no duplicate. Mathlib
semantic and source searches found no matching result; LeanSearch returned HTTP 500,
recorded as unavailable. No change records or forced adaptations are required.

## Second reading by W4

1. Compared the parent module with the repository by diff, and extracted and compared
   its existing theorem signature byte for byte: identical. No definition, existing
   declaration visibility, or public import changed. Only the proof, private helpers,
   proof imports and proof description changed. No change record is required.
2. Compiled both delivered modules locally in import order. Scratch copies with
   `#print axioms` checked both private helpers, the parent, and the new theorem.
   The helpers use only `propext`, `Classical.choice`, `Quot.sound`; the parent and
   refinement additionally use `sorryAx` from the explicitly open statements.
   Exactly one new named theorem has `:= by sorry`; there is no hollow definition
   or forbidden declaration. The parent hole is closed syntactically, not a completed
   axiom-free result: one hole closed and one added, a decomposition with net zero.
3. Read the entire new statement, docstring and node against the existing flat-module,
   proper-support and cartesian tensor-pullback statements. Verified the cited official
   Stacks Tags 05LY, 081G and 0032. The chosen-complex refinement is true and is strictly
   the property-enlargement part of the argument: unlike the parent, it neither creates
   the initial finite-stage complex nor identifies it with arbitrary input G. There
   are finitely many relevant terms, and natural tensor-pullback composition supplies
   differential compatibility. Empty bounds, zero terms, an empty source, a singleton
   index, and equivalent distinct preorder indices cause no exception. The supplied
   i and j ensure the index category is nonempty. Final directed reindexing must be
   taken on a tail above j and transported back with pullback pasting.
   Repeated search with the different phrase "eventual flatness of a fixed coherent
   sheaf and properness of its support over an inverse limit of affine schemes"
   (LeanFinder), `Module.Flat, LinearEquiv` (Loogle), and source searches for
   IsFlatOver, HasSupportProperOver, complex/limit and iso transport found no theorem
   that closes refinement. Loogle confirms the helper already uses the appropriate
   Mathlib `Module.Flat.of_linearEquiv`. No split-off can be closed in a few minutes
   using the available interfaces: the common-stage tensor and complex comparison
   still have to be formalized.
4. Checked the top-down reduction and both original dependencies. The removed direct
   imports are FlatBoundedComplexDescent and ProperSupportDescent; the former node
   is the only original proof dependency no longer needed anywhere in this route.
   ProperSupportDescent remains needed by refinement; FlatModuleDescent remains
   needed there too. Added plain proof imports in refinement for FlatModuleDescent,
   ProperSupportDescent, TensorPullbackFlatProperSupport and Mathlib's directed-final
   reindexing. TensorPullback and BaseChangeConventions are already public transitive
   statement dependencies. The unit sk-thm-picard-semicon has empty realized lists;
   its route is preserved, with no unit statement or step bypassed. Pruning of
   FlatBoundedComplexDescent is conditional on other library users, not a claim of
   measured global closure pruning.
5. Compared both DAG records with the Lean. The parent changes only proof,
   proof_deps and proof_origin. Each dependency union equals the union of step uses.
   The new node has all required creation, provenance, source, search, chapter, unit,
   statement and Lean fields and matches its new declaration. All referenced nodes
   exist and have the recorded Lean or Mathlib interfaces.

Second-reading repair: added the four missing plain proof-dependency imports to
ChosenComplexFlatProperRefinement, so its planned lower nodes remain reachable for
future proof work and are not accidentally pruned. No mathematical statement or
proof term was altered. Scratch probes were removed from the delivery.
