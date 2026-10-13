## What changed

The target statement is unchanged. Its proof composes a natural restricted tensor-pullback
stalk comparison with a natural affine-model stalk tensor transport. The two comparisons
are separate modules, one for each independent part of the original argument. The new
statements quantify natural families, not arbitrary additive equivalences. The target proof
uses AddEquiv.trans and both naturality equations.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.exists_affine_model_tensorPullback_stalk
(new-k1-affine-model-tensor-pullback-stalk). This is a decomposition, not a claim that the
whole argument is sorry-free.

Added AlgebraicGeometry.exists_affine_model_stalk_tensor_transport
(new-e1-affine-model-stalk-tensor-transport), which still has sorry.
AlgebraicGeometry.exists_restricted_tensorPullback_stalk
(new-e1-restricted-tensor-pullback-stalk) is proved from the existing adjunction,
composition and natural tensor-pullback stalk comparison declarations, with no new hole.
There are no sorries in the target or restricted comparison, and one added sorry overall.

## No longer needed

The target no longer directly imports Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk;
it is needed by the restricted comparison. The new restriction module omits Mathlib.AlgebraicGeometry.Modules.Tilde, and the new
affine transport module omits Sheaf.AlgebraicGeometry.TensorPullback: neither statement
needs these imports. No original planned dependency is pruned from
the transitive argument: lem-weil-pbc-spec-tilde-stalk-localization and
lem-weil-pbc-module-stalk-pullback remain beneath the two comparisons. No unrelated
module or unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect in the target was found. The sources were read at
[Stacks 01BH](https://stacks.math.columbia.edu/tag/01BH), property (3), and
[Stacks 0098](https://stacks.math.columbia.edu/tag/0098). The original DAG has localization and
pullback components, but no assembled natural affine chart transport. The new affine
transport isolates that glue without claiming it follows by one application of either
component. Empty V has no z; zero modules and arbitrary, non-flat i are covered by the
stated constructions. The unit has no realized nodes here, and its route stays unchanged.

## New nodes

new-e1-restricted-tensor-pullback-stalk: the underived natural comparison for restriction
to V; it is proved and has no affine chart or model M. It is independent of the affine-model comparison.

new-e1-affine-model-stalk-tensor-transport: transport of R tensor over the original stalk
with F's stalk to R tensor over A with M. It contains no tensor pullback functor, so it
isolates precisely the affine/localization argument from the original plan. Its proof
is given completely in words in the declaration and node.

## Second reading by E1

1. Compared every delivered existing module and node with the repository using diff.
   PASS: the existing theorem signature and docstring are byte for byte unchanged;
   only its proof and proof imports change. There are no changed definitions,
   target interfaces, forced adaptations or change records.
2. Compiled all three modules in import order with lcompile.py, without errors or
   warnings. Searched all delivered Lean for forbidden declarations and sorry:
   exactly one sorry remains, in the named affine transport theorem listed above.
   Scratch-copy #print axioms checks show only propext, Classical.choice and
   Quot.sound for exists_restricted_tensorPullback_stalk, and these plus sorryAx
   for the target and affine transport. PASS as a decomposition, not a completed
   sorry-free target. No definition or arbitrary chosen data has been added.
3. PASS: both intermediate statements are strict parts of the argument: restriction
   has no affine model, and affine transport has no tensorPullback. Checked zero
   modules, identity maps, empty opens (no z), and non-flat morphisms. The affine
   denominators become units in S and then R, so its tensor cancellation and
   naturality hold without flatness. Read its complete fraction-based docstring
   proof and matching node. Verified Stacks 01BH(3) and 0098. Independent searches
   used leanfinder "extension of scalars cancels localization of a module at a
   prime ideal", loogle "IsLocalizedModule, TensorProduct", and grep
   "tensor.*[Ll]ocaliz|[Ll]ocaliz.*tensor", plus rg over lean/. These found
   localization/base-change components, not an assembled natural affine transport.
   Inspected affine_sections_stalk_tensor_presentation and
   affine_tilde_tensor_stalk_bijective: neither states this compatible natural
   family. Closing the remaining hole requires the chart/stalk scalar transports
   and their naturality, not a single application of those declarations.
4. PASS: the target composes the two comparisons and their naturality laws;
   restriction uses adjunction uniqueness and composition followed by the existing
   proved stalk comparison. Imports are limited to signature providers and proof
   dependencies; proof-only imports are plain import. Both old proof dependencies
   remain transitively needed, as the No longer needed section states. Read
   dag/units/sk-thm-picard-duality.json: its realized statement and step lists are
   empty; no unit realization or prescribed step is bypassed.
5. PASS after repair: nodes describe the actual composition and restriction proofs,
   and the pending affine argument. New nodes have source, full proof, searches,
   creation, blueprint, chapter, unit and verbatim Lean statement records. Added
   lem-pc-module-pullback-adjunction to the restriction node's proof_deps and uses,
   since exists_tensorPullbackAdjunction is explicitly used.

Second reading changed only the missing restriction-node dependency and restored
one extra space at the target's proof boundary. No mathematical proof was rewritten.
Holes closed: AlgebraicGeometry.exists_affine_model_tensorPullback_stalk (one).
Holes added: AlgebraicGeometry.exists_affine_model_stalk_tensor_transport (one).
The new restriction comparison is proved with no sorryAx. Net holes closed is zero;
no module is pruned from the targets' import closure.
