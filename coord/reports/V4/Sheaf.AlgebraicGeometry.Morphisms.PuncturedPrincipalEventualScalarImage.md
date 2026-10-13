## What changed

Proved `punctured_principal_eventual_scalar_image` from the depth-two Hartogs
comparison, a Noetherian stabilization argument, and two strictly lower
intermediate statements. Added the modules `DepthThreePunctureHOne` and
`PrincipalThickeningSectionsLift`, each isolating one cohomological part of the
Stacks 0BK0/0AVY/0H3E argument.

## Proved and sorry left

Closed one existing hole: `punctured_principal_eventual_scalar_image`, by reduction
to the two new lemmas and existing Hartogs comparison. This is a decomposition,
not a complete axiom-free proof: one hole closed and two holes added (net -1
before the ledger checks the targets import closure). The
new intermediate declarations `depth_three_puncture_h_one` and
`principal_thickening_sections_lift` remain `sorry`, with nodes
`lem-sbc-depth-three-puncture-h-one` and
`lem-sbc-principal-thickening-sections-lift`; these are strictly smaller
cohomological components, not restatements of the target.

## No longer needed

No imports from the original module were removed; no old proof-dependency
node or module is pruned. Removed the redundant public import
`Mathlib.AlgebraicGeometry.Restrict` from the new `DepthThreePunctureHOne`
module; its needed names are already publicly supplied by Cohomology.Defs. The proof uses the depth
module, finite-etale section transfer, depth-two puncture global sections,
and the two new intermediate modules. The original DAG's direct local
cohomology prose is encapsulated by the two new nodes.

## Where the brief, the DAG or earlier work was wrong

The direct five-step proof plan has no existing Lean declarations for derived
local-cohomology pro-zero systems. It therefore needed two named intermediate
statements to make the reduction compilable; the target statement and its
recursive restriction definition are unchanged.

## New nodes

`lem-sbc-depth-three-puncture-h-one` is the depth-three vanishing input from
Tags 0BK0 and 0AVY. `lem-sbc-principal-thickening-sections-lift` is the finite
stage lifting consequence of Tags 0H3D and 0H3E. Their node files are under
`dag/nodes/sec-smooth-base-change/`.

## Earlier second reading (a previous round; superseded)

The intermediate statements are strictly weaker than the target and compile with the intended interfaces; a second V4 worker should verify the cohomological reductions and node records.


## Second reading by V4

1. Compared the sole existing delivered module with the repository using diff.
   Its existing theorem signature is byte for byte unchanged, as is the entire
   recursive restriction definition. There are no interface changes, forced
   adaptations, changes to data constructions, or change records. Verdict: pass.
2. Compiled all three delivered modules with lcompile.py. Checked the sources
   for forbidden declarations and holes: precisely the two new public theorems
   have `:= by sorry`; none occurs in a definition or private helper. A scratch
   axiom check of the recursive definition, item theorem and both new theorems
   shows only propext, Classical.choice, Quot.sound and (for the three theorems)
   sorryAx. The definition uses no sorryAx. Verdict: valid reduction with open
   dependencies, not an axiom-free completed theorem.
3. Read Stacks 0BK0(2), 0AVY Lemma 47.11.1, 0H3D and 0H3E. The first new theorem
   isolates H^1 vanishing, independent of principal thickenings. The second
   takes H^1 vanishing and a torsion bound as hypotheses, lifts to ambient
   sections, and makes no depth, locality or Noetherian assumption. It is a
   proper intermediate component, not a renamed copy of the item. Tested
   empty opens, c=0, g=0, nilpotent and invertible g in the mathematical
   argument. In particular, hkill localizes exactly even for non-Noetherian R.
   Independent leanfinder, loogle and grep searches and reads of both source
   roots found no exact existing replacement; Mathlib's kernel stabilization
   lemmas supply the already-proved private helper. Neither cohomological
   component could be closed in a short proof with the existing infrastructure.
   Verdict: both true, needed intermediate assertions with sourced full proofs.
4. Read from the item downward through Hartogs, stabilization and the two new
   lemmas. Each import remaining is used by signatures or proofs; proof-only
   imports in the item remain plain imports. No original dependency is unused.
   Read dag/units/sk-prop-input-spreading.json: the new reduction is below the
   unit level, retains the purity/depth route, and alters no realized entry.
   Verdict: no unit bypass; no original modules pruned.
5. Repaired the item's proof steps so their uses have exactly the recorded
   proof_deps union and explicitly name the two new intermediate declarations.
   Repaired copied, incorrect new-node proof/statement dependency lists: the
   H^1 lemma does not depend on depth-two Hartogs; the lifting lemma does not
   depend on depth-three vanishing or Noetherianity. Replaced its copied depth
   proof with the actual shifted-index complex factorization, quotient-map
   identification and recursion argument. Made both new lean.statement fields
   literal multiline signatures, and recorded independent search results.
   Verdict: node records now agree with the delivered Lean and sourced proof
   plans. No existing node statement was changed.

Changed the lifting docstring to the explicit 0H3D factorization proving the
exact finite gap c; removed the redundant import from the new H^1 module;
repaired DAG records, searches and the decomposition accounting above. The
existing item's Lean proof itself needed no repair.

The first dry run required the distinct LeanSearch search kind in both new
nodes. Ran both appropriate queries: the service returned Internal Server
Error, recorded as unavailable without a mathematical search verdict. The
Loogle/LeanFinder and source grep checks above supplied the available search.
