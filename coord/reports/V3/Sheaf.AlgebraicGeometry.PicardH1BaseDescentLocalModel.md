## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.picard_h1_base_descent_local_model`
with a complete Lean reduction to two strictly smaller geometric statements. The
existing theorem's signature and visibility are unchanged. The proof constructs the
scalar differential vector, proves its homogeneity from three linear maps, proves
strict perfectness from the term isomorphisms, proves negative terms are zero using
the empty free-module universal property, and combines the annihilation and
cohomology-comparison data.

Added `Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel` for the common target
trivializations and minimal source representative, and
`Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison` for the joint degree-one
map on a fixed affine source model. Both contain one named theorem with a source,
complete proof in words, and matching DAG node. No new definition chooses data
from an unproved existence statement: all witnesses are used inside theorem proofs.

The top module imports these two proof modules. The second reading added proof-only
imports of `FlatDerivedStructureUnit` and `Mathlib.RingTheory.LocalRing.Module`
to the fixed-model module, with the corresponding derived-unit node dependency.
The two new module docstrings now carry their blueprint node identifiers.

The top module imports these two proof modules. The first intermediate supplies
neither b nor a cohomology square; the second chooses neither an open neighbourhood
nor a source complex or its bases. Thus neither is a renamed copy of the item.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.picard_h1_base_descent_local_model`
(node `lem-sc-picard-h1-base-descent-local-model`). Its own body has no sorry.

Added and left with sorry:

- `AlgebraicGeometry.Scheme.picard_h1_common_minimal_model`
  (node `lem-sc-picard-h1-common-minimal-model`).
- `AlgebraicGeometry.Scheme.picard_h1_fixed_model_comparison`
  (node `lem-sc-picard-h1-fixed-model-comparison`).

This is a decomposition: one upper hole closed and two geometric holes added,
not a sorry-free proof of the geometry. There are no other new holes, no definition
holes, and no untouched holes in the item's module. Edge cases checked in the
statements and their proofs in words: n=0, m=0, zero higher ranks, empty base schemes
(the marked point hypothesis excludes them), and nonreduced affine bases. No
injectivity on the joint H-one map is assumed.

## No longer needed

Removed from the top module the direct proof imports:

- `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`
- `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`
- `Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections`
- `Sheaf.AlgebraicGeometry.FieldPullbackRankOneTrivial`

These modules and their nodes remain necessary through the two intermediate
modules; this is a redistribution of proof dependencies, not pruning them from the
import closure. No geometric module or original DAG dependency can yet be declared
unneeded. The original unit route is preserved; its realized fields have no binding
nodes at this local-model level. Globally pruned modules: none.

The old direct `proof_deps` no longer used directly by the top proof are:

- `def-amb-finite-locally-free-module`
- `def-pc-base-change`
- `def-pc-derived-direct-image`
- `def-pc-module-pullback`
- `def-sc-invertible-module`
- `def-sc-structure-sheaf-cohomology-pullback`
- `def-weil-residue-field`
- `lem-pc-cohomology-sections-affine-base`
- `lem-pc-module-pullback-adjunction`
- `lem-pc-perfect-affine-map-representative`
- `lem-pc-rf-perfect-base-change`
- `lem-sc-field-pullback-rank-one-trivial`
- `lem-sc-perfect-finite-free-residue-model`

These remain statement dependencies or dependencies of the intermediates; the
only old direct proof dependency retained is `def-pc-perfect-complex`.
The new derived-unit dependency is an existing theorem of the same cube unit,
used for its canonical degree-zero fibre comparison, not a replacement route.

## Where the brief, the DAG or earlier work was wrong

No existing statement was changed or disputed. The old plan requires shrinking
when choosing finite-free target models. A comparison lemma for a *fixed* affine
source cannot quietly shrink that affine again. The second intermediate instead
uses bounded finite-projective target representatives on the supplied affine, using
`PerfectAffineBoundedProjective` and `AffineLocalizedDerivedSheafification`:
each degree-one target embeds into a finite free ambient module, and beta projects
back before passing to cohomology. At residue level a linear retraction onto cycles
exists over the field and is the identity on the source chain-map image. The
universal structure-unit condition, rather than projectivity of H-zero alone,
justifies cancelling the target degree-zero complement. These details are included
explicitly in its docstring and node proof.

LeanSearch was attempted for both geometric statements and reported Internal Server
Error; LeanFinder, Loogle and source/blueprint searches were available. The ancestor
script returned None for the item's module-based creation history; the new nodes
inherit the already recorded blueprint ancestor `thm-sc-theorem-of-cube` and prepend
the present node to its existing via list. The source Tag 0BF2 was read directly at
its public Stacks page because the literature source checkout is absent here.

## New nodes

`lem-sc-picard-h1-common-minimal-model`: common target trivializations and a bounded
minimal source complex, all term ranks and zero residue differential; in
`lean/Sheaf/AlgebraicGeometry/PicardH1CommonMinimalModel.lean`.

`lem-sc-picard-h1-fixed-model-comparison`: annihilation and the canonical residue
H-one square for a supplied affine minimal source complex; in
`lean/Sheaf/AlgebraicGeometry/PicardH1FixedModelComparison.lean`.

Both nodes are under `dag/nodes/sec-abelian-varieties/`, inherit the item's chapter
and unit, and retain the source's non-injectivity construction. No change records
or forced adaptations are required.

## Second reading by V3

1. **Visible declarations: pass.** Read the repository and sandbox modules and their
   diff. The entire existing `picard_h1_base_descent_local_model` signature is byte
   for byte identical, including both universal adjunction-unit hypotheses, descent
   hypotheses, localized derived instances, and the precise cohomology square.
   Only its proof, proof imports, heartbeat option and proof account changed.
   There are no changed definitions, forced adaptations or change records.
   Both intermediate signatures match their node `lean.statement` verbatim.

2. **Kernel check and holes: pass as a decomposition.** Compiled all three modules
   in import order with lcompile.py. Read the proof: the term isomorphisms give the
   required retracts; freeHomEquiv proves the empty free term zero; hb at 1 gives
   b(d)=0; the two scalar-map linearity rewrites prove the formula for every a.
   Scratch copies with `#print axioms` for each of the three declarations report
   only propext, Classical.choice, Quot.sound and sorryAx. The only explicit holes
   are the two public named intermediate theorems listed above. No axiom, unsafe,
   opaque, implemented_by, extern, definition hole or arbitrary data definition
   is added. The upper theorem is not axiom-complete: its two geometric inputs
   remain open. Neither remaining geometric theorem admits a few-minute closure
   from the present declarations.

3. **Intermediate statements: pass, proof accounts repaired.** Read Stacks Tag
   0BF2 (the complexes and chain maps before its injectivity step), both new node
   statements and every hypothesis of both Lean theorems. The common-model lemma
   gives no joint map or comparison square. Rank one follows by pulling a descended
   finite-free presentation to a point of a nonempty fibre; the source is trivial
   by the existing field rank-one theorem. Perfect direct-image base change and
   exists_finiteFreeResidueModel give the ranks. The dimension formula for a finite
   residue complex then kills both adjacent differential ranks. The comparison
   lemma fixes U,K,e0,e1 and neither supplies nor shrinks them; it requires no H-one
   injectivity. Its fixed-affine projective construction is stronger than simply
   repeating the source's permission to shrink. In each cancellation step, residue
   injectivity gives a split injection over the local ring, with finite free
   cokernel; the finitely presented locally free cokernel is finite projective on
   the affine, so the splitting is global. The derived unit's fibre comparison is
   supplied by exists_flat_derived_structure_unit. Its hypotheses hold because
   each base-changed target morphism is flat, proper and hence quasi-compact and
   separated. Source minimality puts each residue chain-map image in target cycles,
   so a field-linear projection onto cycles leaves that image unchanged. The
   scalar comparing fibre trivializations is constant because the universal unit
   identifies fibre global functions with the residue field; it is nonzero because
   both sections trivialize the invertible bundle. This justifies beta's scalar
   normalization and the exact canonical structure-sheaf square.
   Checked n=0 (empty product, q=0), m=0 (minimality forces source H-one zero),
   negative/zero term ranks and nonreduced bases. The marked point rules out an
   empty W or U, and the universal units rule out empty geometric fibres; no
   reducedness assumption enters the local splitting argument. Searched again
   with LeanFinder for universal connectiveness and degree-zero units, Loogle for
   IsPerfect, and msearch grep for the residue split-injection criterion; results
   provide abstract tools, not either new geometric statement. Searched both Lean
   roots and the upstream checkout for unimodular, split injective, unit degree
   zero and Picard models. FlatDerivedStructureUnit is an existing input, now cited;
   the downstream Picard cycle-realization statements import this item and cannot
   close it without a cycle. No duplicated statement or disguised restatement found.

4. **Route and pruning: pass.** Read sk-prop-av-cube.json and its realized fields
   (empty statement/step bindings). The finite-free source and representing-chain-map
   route of 0BF2 is retained below the unit level. Public imports are for signature
   notions; the geometric proof imports are private. The report now lists every old
   proof_deps entry absent from the new top-level proof_deps, and distinguishes that
   redistribution from actual pruning. No module is claimed pruned globally.

5. **Node agreement: pass after repair.** The original node changes only proof,
   proof_deps and proof_origin. Its four steps follow the actual Lean reduction;
   the elementary scalar and empty-free-module arguments are visible in the body.
   Both new nodes have self-contained statements, sources, proof steps, dependency
   unions, creation/blueprint records, searches and exact Lean signatures. Added
   lem-sc-flat-derived-structure-unit to the fixed-model first step and proof_deps
   so the canonical derived-unit input is recorded, rather than attributed to the
   adjunction statement alone. The new module headers now include their blueprint
   identifiers. Search evidence remains in searches.jsonl.

**Changes by the second reader:** added the two module blueprint labels; made
negative-term and degree-zero cancellation over the entire affine explicit; cited
and imported the existing derived structure-unit theorem and the Mathlib local-ring
split-injection criterion; synchronized the fixed-model node's proof dependencies;
completed the old-dependency accounting above. No Lean theorem signature or proof
body was changed. One upper hole is closed, two lower holes remain: decomposition,
not a completed proof, and no globally pruned modules.
