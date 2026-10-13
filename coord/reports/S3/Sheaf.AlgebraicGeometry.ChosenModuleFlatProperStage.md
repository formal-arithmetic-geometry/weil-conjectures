## What changed

Proved the body of `AlgebraicGeometry.exists_eventually_chosen_module_flat_proper`
in `Sheaf.AlgebraicGeometry.ChosenModuleFlatProperStage`, without changing its signature,
visibility, universes or existing docstring. The proof applies flatness descent to the
fixed module on stage j, obtains a proper-support stage separately, chooses their
common directed upper bound, and proves both properties at each later stage.

Three proved private helpers handle module-isomorphism invariance of proper support,
proper-support preservation in an arbitrary cartesian square, and comparison of two
cartesian models. They use the existing finite-type support-pullback theorem,
independence of the closed subscheme structure, proper base change and tensor-pullback
composition. Finite presentation of the tensor pullbacks is proved using uniqueness
of left adjoints and the proved native pullback instance from Modules.FiniteDescent.

Added `Sheaf.AlgebraicGeometry.FlatModuleDescentPreorder`, containing one public
flatness-only theorem. It extends the existing partial-order flat descent theorem to
directed preorders and arbitrary cartesian models. This is strictly a part of the
argument: it has no proper-support assumption or conclusion, and it does not mention
a chosen intermediate base-change stage. Its natural-language proof and node record
the final-directed-poset reindexing, partial-order descent, and propagation back to
arbitrary later stages. Updated the original DAG proof to match the Lean argument.

Both modules compile cleanly through lcompile.py. The deliver3.py --no-push dry run
printed OK, with only the independent second reading still pending and nothing pushed. No target or existing statement,
definition, attribute or visibility has changed. No consumer adaptation is needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_eventually_chosen_module_flat_proper`
(node `lem-pc-chosen-module-flat-proper-stage`). Its proof has no local sorry.
The three private helpers are proved.

Added exactly one hole:
`AlgebraicGeometry.exists_eventually_isFlatOver_of_isPullback_limit_preorder`
(node `lem-pc-flat-module-descent-preorder`), in its own new module, with the entire
proof `by sorry`. It is the only textual sorry left in the delivery.
This is a one-hole decomposition (one upper hole closed and one lower hole added),
not a claim that all dependencies have been proved. The proper-support descent,
cartesian comparison and preservation argument, and the directed combination are
complete Lean proofs from the stated library theorems.

Edge cases checked in the argument: zero modules have empty support, whose closed
subscheme base change remains proper; empty sources cause no exception to the support
or flatness predicates. An empty index type cannot have the supplied stage i (or j).
For the new flatness theorem, one-stage systems reduce to invariance under cartesian
model isomorphism. Equivalent but distinct objects of a preorder need no antisymmetry:
the final partial order supplies descent, while preservation treats any later object
of the original preorder, whether or not it is in the image of the final functor.
No flatness of any transition map or properness of the whole source is assumed.

## No longer needed

Removed the direct proof imports:

- `Sheaf.AlgebraicGeometry.FlatModuleDescent`: the item now uses the new preorder and
  cartesian-model interface. Its node `lem-pc-flat-module-descent` remains a planned
  dependency of the new flatness node; it is not mathematically discarded.
- `Sheaf.AlgebraicGeometry.TensorPullbackFlatProperSupport`: the combined preservation
  statement `lem-pc-tensor-pullback-flat-proper-support` is unnecessary. Flatness is
  supplied at every later stage by the new interface, and proper support alone is
  preserved by the proved local cartesian helper. No realization of this unit names
  the discarded node.
- `Mathlib.CategoryTheory.Presentable.Directed`: final-poset reindexing is confined to
  the new flatness node. The corresponding Mathlib leaf
  `lem-weil-pbc-filtered-category-exists-directed-final` remains in that node's plan,
  but is no longer a direct proof dependency of the item.

No original public import was removed. Tensor-pullback composition and the base-change
conventions remain necessary and are explicitly used. The proper-support descent
module remains necessary. The library may reach removed modules through other imports;
this report claims direct pruning, not global unreachability.

## Where the brief, the DAG or earlier work was wrong

The original flat-module descent declaration assumes PartialOrder, whereas this item
assumes only Preorder. Its native pullback interface also differs from the chosen
moduleBaseChange objects. Proper-support descent accepts the preorder but still needs
cartesian-model comparison. These gaps are now represented explicitly: the flatness
gap is the new theorem, and proper-support comparison is proved locally.

The source checkout has the recently landed
`Sheaf.AlgebraicGeometry.PullbackModelFlatnessComparison` and
`Sheaf.AlgebraicGeometry.TensorPullbackFinitePresentation`, but their compiled modules
were absent from the last green local snapshot during this work. They were not copied
into the delivery or used as unavailable imports. The new flatness node cites the
existing comparison node in its proof plan. The item proves the elementary native-to-
tensor finite-presentation transfer directly against the available library.

LeanSearch returned Internal Server Error and is recorded as unavailable. LeanFinder
and a Mathlib source grep found no matching flat-module descent theorem. Blueprint
searches for flat module, 05LY and cartesian flatness found no duplicate statement;
the existing flat-module descent is the partial-order specialization. The ancestor
script returns None for this stage-3 module-created node; the new node inherits the
explicit blueprint ancestor recorded on the item's node. The unit record
sk-thm-picard-semicon has no realized-node entries naming this item or its discarded
combined-preservation dependency; its route is preserved.

Source statements were read at Stacks Tags 05LY, 0032 and 01U8, with the exact labels
verified against the source tex files downloaded into the sandbox scratchpad.
They supply the fixed-
module flatness descent, final directed index and base-change preservation used by
the new node. No source or statement dispute was found.

## New nodes

`lem-pc-flat-module-descent-preorder`, in
`dag/nodes/sec-picard-framework/lem-pc-flat-module-descent-preorder.json`, states only
flatness descent for a fixed finitely presented module over a directed preorder,
allowing arbitrary cartesian models at the limit and at later stages. Its module is
`lean/Sheaf/AlgebraicGeometry/FlatModuleDescentPreorder.lean`. It carries the source,
complete proof plan, exact Lean signature and actual searches from searches.jsonl.
No change record is needed: no existing interface was changed.

## Second reading by S3

1. Compared both delivered Lean modules with the repository versions. The existing target
   declaration and all existing declarations retain byte-for-byte identical signatures,
   visibility, universes and docstrings; the only changed existing body is the target proof.
   The new module contains the separately recorded theorem and its matching node.
   Verdict: pass.

2. Compiled both modules with `lcompile.py --all`; compilation succeeds without errors or
   warnings. Searched the delivered Lean files for forbidden declarations and found none.
   The target proof and its private helpers contain no `sorry`; the sole remaining `sorry`
   is the named theorem `exists_eventually_isFlatOver_of_isPullback_limit_preorder`, which
   has a docstring, node and source. Verdict: pass.

3. Checked the target proof route against the node proof and its dependencies. The target
   statement is unchanged and the new preorder flatness theorem is strictly weaker than the
   target: it asserts flatness only, with no proper-support conclusion or chosen-stage
   condition. The theorem is not duplicated by an existing library declaration. Verdict:
   pass, with the new theorem intentionally split off as one lower hole.

4. Checked pruning and shortest-route choices. The target directly uses the preorder
   flatness interface, proper-support descent, explicit cartesian support transport and
   tensor-pullback composition. The three direct imports removed from the old proof are
   recorded under `## No longer needed`; the corresponding old combined-preservation node
   is not used. The unit route remains the flatness descent followed by proper-support
   descent and later-stage preservation. Verdict: pass.

5. Checked that the DAG files agree with the Lean declarations, including proof steps,
   proof dependencies, source, blueprint ancestry, module and declaration fields. The new
   node is marked `split` and records the exact theorem signature and its proof plan.
   Verdict: pass.

Changed during second reading: added this review section only; no Lean, DAG or import
changes were needed.
