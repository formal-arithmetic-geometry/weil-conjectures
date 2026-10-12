## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.exists_smooth_stage_of_affine_limit`
by a compiling finite affine-source-cover argument. The signature and all public imports
are unchanged. Added a proof-only import of
`Sheaf.AlgebraicGeometry.Morphisms.AffineSourceLimitSmoothStage`.
The affine-source module imports the algebra descent and upstream comparison modules
proof-only, matching its planned dependencies; redundant direct affine-transition
and pullback-pasting imports were removed from the new work.
Two proved private helpers implement smoothness after further base change and after
restricting the source to an open chart. The proof identifies the supplied pullback,
chooses a finite affine cover, obtains one stage per chart, chooses a common refinement
in `Over i`, and uses source locality on the pulled-back cover.

Completed the earlier affine-source module with its required DAG node and source proof.
The node for the assigned theorem now records exactly this assembly.
Both modules compile through lcompile.py in import order without warnings.

## Proved and sorry left

Closed the single original hole, `AlgebraicGeometry.Scheme.exists_smooth_stage_of_affine_limit`
(node `lem-sbc-affine-limit-smooth-stage`). No sorry remains in the assigned module.
The private helpers `smooth_snd_comp` and `smooth_snd_source` are fully proved.

One new hole is split off:
`AlgebraicGeometry.Scheme.exists_smooth_stage_of_affine_source_limit`
(node `lem-sbc-affine-source-limit-smooth-stage`). This is strictly the affine-source
subproblem: it assumes `IsAffine P`, while the original theorem allows arbitrary P.
The parent theorem supplies and assembles a finite cover by such affine sources.
The canonical-pullback smoothness hypothesis is used via the comparison isomorphism,
not assumed anew. This is a decomposition (one hole closed, one added in the delivered sources),
not a claim of an unconditional sorry-free proof of eventual smoothness.

Edge cases checked: the cofiltered finite-image lemma includes an empty image;
no nonempty-source assumption is introduced. Empty charts use the smooth zero algebra.
Affineness of the source is not mistaken for affineness of its map to a non-affine base:
the remaining theorem explicitly uses a finite base cover and affine covers of its
inverse images. The hypotheses on p are preserved on open charts by Mathlib instances.

## No longer needed

No original imports removed and no globally pruned modules claimed.
Removed the redundant new proof import `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting`
from the parent. The new affine-source module needs no direct import of
`Mathlib.AlgebraicGeometry.AffineTransitionLimit`: the upstream comparison module
already publicly imports it. These are import cleanups, not globally pruned modules. The original algebra descent,
global-sections continuity, and comparison nodes are not used directly by the parent:
`lem-weil-pbc-limit-global-sections-colimit`,
`lem-weil-pbc-smooth-algebra-filtered-colimit-descent`, and `thm-pd-spreading-out`.
They remain required by the new affine-source node, so are not pruned from the argument.
Their modules are not imported into the parent merely for the old planned route.
`def-sbc-smooth-morphisms` stays used through Mathlib.

## Where the brief, the DAG or earlier work was wrong

The earlier ABANDON claimed finite-cover and common-stage gluing could not be completed
because the APIs were absent. Mathlib already supplies finiteSubcover,
IsCofiltered.inf_objs_exists, the cofiltered Over instance, pullback-pasting isomorphisms,
and IsZariskiLocalAtSource.of_openCover. These now prove that part of the argument.
The earlier sandbox had no node for its new theorem and left the main hole untouched;
both defects are repaired.

The blueprint unit route is unchanged: this is the affine-chart portion of the
spreading unit's limit reduction. The new node retains the original algebra-descent
and 01ZM comparison route as generic tools. Those tools should not be deleted.
No interface change, forced adaptation, or data chosen from an unproved existence
theorem occurs.

## New nodes

`lem-sbc-affine-source-limit-smooth-stage` in
`dag/nodes/sec-smooth-base-change/lem-sbc-affine-source-limit-smooth-stage.json`
states eventual smoothness only for an affine source model, in the new module
`Sheaf.AlgebraicGeometry.Morphisms.AffineSourceLimitSmoothStage`.
Its docstring and numbered proof cover base restriction, filtered-colimit algebra
descent, descent of the comparison isomorphism and inverse equations, and the finite
base-chart assembly. Source: Stacks 0C0C, 0CAQ, and 01ZM(2)-(3).
Mathlib/source-library and blueprint searches found no applicable duplicate.
There are no change records because all existing interfaces remain unchanged.

## Second reading by V1

1. Compared the complete parent module by diff with the repository version. The sole
   existing theorem signature is byte for byte unchanged; its public imports and
   visibility are unchanged. The second module is new. No existing definitions or
   target statements changed, so no change record or forced adaptation is needed.
   Verdict: pass.
2. Compiled both modules through lcompile.py in dependency order, without warnings.
   Read all proof terms and checked for forbidden declarations and hollow definitions:
   none. Scratch #print axioms checks show only propext, Classical.choice, Quot.sound
   for both private helpers; the parent and new theorem additionally have sorryAx,
   as expected from the single named affine-source hole. All data selected from
   that theorem occur locally in a proposition proof, not in any definition.
   Verdict: pass as a decomposition, not an unconditional proof.
3. Read the affine-source signature, its docstring and node together. It is the
   genuine affine-source subproblem; the parent proves finite covering and common-stage
   assembly rather than merely renaming its original statement. Checked empty schemes,
   the singleton diagram (where the original stage suffices), identity transitions,
   and non-affine bases. In particular, affineness of P does not assert affineness of p.
   Checked Stacks [0C0C](https://stacks.math.columbia.edu/tag/0C0C),
   [0CAQ](https://stacks.math.columbia.edu/tag/0CAQ), and
   [01ZM](https://stacks.math.columbia.edu/tag/01ZM) against the written argument.
   Independent leanfinder query for descent of a finitely presented affine scheme
   along filtered colimits returned finite-presentation and smoothness characterizations;
   loogle query `"Smooth", "colimit"` returned no hits. msearch grep and rg of
   Mathlib, Sheaf and the upstream library found faithfully-flat descent and the
   specialized NoetherianApproximation route, neither applicable to the hypotheses.
   No duplicate or quick closure of the remaining algebra/comparison argument found.
   Verdict: pass, one strictly narrower theorem remains open.
4. Followed the proof from the general theorem down: comparison with the canonical
   pullback, finite affine source cover, chart descent, common object in Over i,
   base-change pasting, source locality. The proof uses existing Mathlib APIs for
   all assembly steps. Checked the old proof_deps against the report: all three
   algebra/continuity/comparison dependencies moved below the affine-source node
   and are named under No longer needed; the smoothness definition stays used.
   Read dag/units/sk-prop-input-spreading.json: its realized entries are empty;
   no realized statement or step is bypassed or changed, and limit reduction stays.
   Verdict: pass after import cleanup.
5. Checked existing node edits are confined to proof/proof_deps/proof_origin;
   the theorem's recorded Lean signature and mathematical statement stay unchanged.
   Checked the new node's source, statement dependencies, proof dependency union,
   search records, chapter/unit, blueprint origin, created.item and verbatim Lean
   signature. Corrected an undefined `f` in its proof narrative to the canonical
   limit projection. Added the algebra-descent and upstream comparison imports
   as proof-only imports in its module so the planned dependencies are available.
   Verdict: pass after repair.

Second-reading changes: repaired proof-dependency imports in the new module,
removed redundant direct imports from the new work, corrected the new node's
proof narrative, and clarified the report's decomposition accounting. The actual
finite-cover proof and all theorem signatures were retained. Progress figures
for the target import closure remain the pinned sorry ledger's responsibility;
this report counts the holes changed in the delivered sources only.
