## What changed

Proved the body of
`AlgebraicGeometry.exists_eventually_isFlatOver_of_isPullback_limit_preorder`
without changing its signature or any definition. The proof compares the given limit
model with the canonical one, obtains one flat stage, and proves flatness at every
later stage by relative-flatness base change, cartesian pasting, tensor-pullback
composition, and cartesian-model comparison. Added proof-only imports of
`FlatModuleDescentPreorderStage`, `PullbackModelFlatnessComparison`,
`RelativelyFlatModulePullback`, and `TensorPullbackFinitePresentation`.

Added `Sheaf.AlgebraicGeometry.FlatModuleDescentPreorderStage` with a named
one-stage-existence theorem. Existing public imports are retained for the signature.
No construction chooses arbitrary data from an unproved existence theorem: the
existential stage is eliminated only within a proof of a proposition, and all
schemes used in the proof are actual categorical pullbacks.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_eventually_isFlatOver_of_isPullback_limit_preorder`.
Added one hole:
`AlgebraicGeometry.exists_isFlatOver_of_isPullback_limit_preorder_stage`, node
`lem-pc-flat-module-descent-preorder-stage`, in
`Sheaf.AlgebraicGeometry.FlatModuleDescentPreorderStage`.
This is a decomposition (one hole closed, one added, net zero), not an axiom-free
proof of preorder descent. The remaining theorem asserts only existence of one
canonical flat stage; propagation to every later stage and independence of the
cartesian model are proved in the original module. Its docstring gives the complete
mathematical reduction to directed-poset descent.

Removed the first worker's proposed hole
`AlgebraicGeometry.exists_eventually_isFlatOver_of_isPullback_limit_preorder_canonical`
and its proposed node `lem-pc-flat-module-descent-preorder-canonical-core` before
delivery. Neither was part of the baseline library.

## No longer needed

No baseline import was removed and no library module is globally pruned.
The original node no longer directly uses these old proof dependencies:
`lem-pc-flat-module-descent`,
`lem-weil-pbc-filtered-category-exists-directed-final`, and
`lem-weil-pbc-initial-functor-limit`.
They remain in the proof plan of the one-stage existence node; this does not claim
that those dependencies are globally unnecessary.
All other original proof dependencies are retained and used by the original proof.
The proposed `FlatModuleDescentPreorderCanonical` module is discarded, not pruned
from the baseline library.

## Where the brief, the DAG or earlier work was wrong

The first worker recorded only a name search for the new core, abbreviated its
Lean statement with an ellipsis, omitted a complete pruning inventory, and called
the upper theorem proved without distinguishing the net-zero decomposition.
Its reduction was correct but left both one-stage existence and later-stage
propagation inside the new hole. The second reading proves propagation using
existing library declarations, and leaves only one-stage existence open.
LeanSearch returned an internal server error; Lean Finder, Loogle, and grep ran.
Their hits concern flat morphisms, tensor-product flatness, and faithfully-flat
descent, not the remaining sheaf-module inverse-limit descent theorem.

## New nodes

`lem-pc-flat-module-descent-preorder-stage` states one-stage canonical relative
flatness descent for a directed preorder. Its complete signature is recorded
verbatim. Its two proof steps are final directed-poset reindexing with pullback
identifications, followed by the existing partial-order descent theorem and
identification at one image stage. It shares the original chapter and unit and
records all statement dependencies, source, proof dependencies, creation data,
blueprint provenance, and actual Mathlib searches. No change record is required:
no existing statement, definition, visibility, or public import changed.

## Second reading by T3

1. Compared the delivered original module with the repository using diff and checked
   its theorem signature byte for byte. Only proof bodies and proof-only imports
   change. No existing definition or statement changes. Verdict: pass.
2. Compiled both delivered modules individually in import order using lcompile.py.
   Scanned for forbidden declarations and holes: precisely one named theorem has
   `sorry`, and no definition has a hole. Checked both declarations using scratch
   copies with `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`,
   and `sorryAx` from the remaining dependency occur. Verdict: pass as decomposition.
3. Checked the remaining statement mathematically against the partial-order descent
   theorem and final reindexing. The chosen i excludes an empty index category;
   a singleton index reduces to the assumed flatness, zero modules and empty sources
   are flat, and equivalent distinct preorder objects require no antisymmetry.
   Base change supplies finite presentation and quasi-coherence, with no transition
   flatness required. Searched Mathlib by semantic Lean Finder, tensor-flatness
   Loogle, and descent/limit grep queries, and searched both the project and upstream
   sources. No existing preorder one-stage declaration was found. Verdict: pass;
   the one-stage lemma is strictly a part of the argument, not an all-stages restatement.
4. Read from the upper theorem downward. Used already proved comparison,
   tensor-pullback finite presentation/composition, and relative-flatness base-change
   declarations. Every added import is proof-only and used; retained public imports
   serve the unchanged signature. Listed all three removed direct proof dependencies.
   Read `dag/units/sk-thm-picard-semicon.json`: its realized statement/step lists
   contain no nodes, and no unit route or realization is changed. Verdict: pass.
5. Checked node proof steps and the union of their uses against proof_deps, and checked
   sources, origin, chapter/unit, searches, blueprint provenance, and the verbatim
   signature of the new node. Verdict: pass after repairing metadata.

Changed the residual theorem from eventual flatness in canonical models to flatness
at one canonical stage; proved propagation and comparison in the original module;
replaced the provisional core module/node; completed the residual docstring proof,
search records, signature metadata, pruning inventory, and decomposition accounting.
