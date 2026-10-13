## What changed

Proved both public theorems in Sheaf.AlgebraicGeometry.OpenUnionModuleImagePullbackCore,
with every existing signature and visibility unchanged. The sectionwise proof transports
Mathlib's two-open sheaf pullback through the direct-image comparisons. The assembly proof
uses its given sectionwise gluing hypothesis, proves commutativity from the restriction
comparison, and reflects the evaluated limits to module presheaves and module sheaves.
The two private helpers are fully proved. No definitions or other modules changed.

Replaced the direct Mathlib IsPullback.Defs import with proof-only imports of
Mathlib.CategoryTheory.Limits.Types.Pullbacks,
Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits, and
Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections.
Kept both original Sheaf imports. Updated both node proofs; the assembly node now cites
the section-restriction comparison rather than the sectionwise theorem, because its
own hypothesis already supplies the gluing data.

## Proved and sorry left

Closed both original holes:
- AlgebraicGeometry.schemeOpenUnionModuleImage_sectionwise_gluing
  (lem-pc-open-union-module-image-pullback-core-sectionwise).
- AlgebraicGeometry.schemeOpenUnionModuleImage_isPullback_of_sectionwise
  (lem-pc-open-union-module-image-pullback-core-assembly).

No sorry remains in the delivered module. Added zero holes and split off zero statements.
This is a proof, not a decomposition. The source comparison theorem is already proved.
Local/server-wrapper single-file compilation passed without warnings (7.4 seconds).
The delivery dry run performs the axiom probe as its final validation.

## No longer needed

Removed the redundant direct import
Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs; the required declarations
are provided by the proof imports.

The assembly proof does not use
AlgebraicGeometry.schemeOpenUnionModuleImage_sectionwise_gluing or its node
lem-pc-open-union-module-image-pullback-core-sectionwise: it uses the hypothesis h.
The sectionwise theorem itself remains proved and available for its other callers, so
no project module is claimed to leave the targets' import closure. No Sheaf module or
source-library module import was removed. No unit statement or realized step was bypassed;
the unit record sk-thm-picard-duality has no realized nodes in these two helper slots.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface found. The assembly node's old dependency on
the sectionwise theorem was unnecessary because sectionwise gluing is a hypothesis of
the assembly theorem. Mathlib already provides the gluing and assembly machinery, so
no new statements or witness constructions were needed. The proofs handle arbitrary
opens, including empty, equal, and nested opens, without additional hypotheses.

Searches run: LeanFinder for unique gluing on a two-open union, Loogle for
CategoryTheory.Limits.Types.isPullback_iff, and the project search wrapper's grep for
existsUnique_gluing and evaluationJointlyReflectsLimits. Read the matching Mathlib
sources and the full section-restriction comparison module and node. The cited Stacks
source files are not populated in this clone; read the official tag pages instead:
https://stacks.math.columbia.edu/tag/01EB (the sheaf-condition kernel argument) and
https://stacks.math.columbia.edu/tag/08BV (the sectionwise restriction/direct-image
sequence). The existing source citations are retained.

## Second reading by C1

1. Compared the only delivered Lean module with the repository using diff and
   checked both theorem signatures as exact byte strings through `:= by`.
   Both are unchanged, including all universes, hypotheses, conclusions and
   visibility. Existing definitions and docstrings are unchanged. Verdict: pass.
2. Compiled the delivered module with lcompile.py without errors or warnings.
   A scratch copy with #print axioms for both public theorems reports exactly
   propext, Classical.choice and Quot.sound, with no sorryAx. Read both private
   helpers: ordinary_gluing_pullback uses the underlying additive sheaf's
   isLimitPullbackCone; imageRestriction_comp cancels an evaluated comparison
   isomorphism and uses restriction-map composition. No sorry, new axiom,
   forbidden declaration, hollow definition or arbitrary witness construction
   occurs. Verdict: pass.
3. No statement was split off and no new node or public declaration was added.
   Checked that P(A) = A intersect T, the comparison is an actual isomorphism,
   and the two-open sheaf pullback applies also to empty, equal and nested opens.
   Read Mathlib's Types.exists_of_isPullback, Types.ext_of_isPullback and
   Types.isPullback_iff, and searched the project and upstream algebraic-geometry
   sources for restriction composition and sectionwise pullbacks. No duplicate
   public statement is introduced. Verdict: pass.
4. The sectionwise proof transports ordinary gluing across e(A); existence is
   transported back by its inverse and uniqueness by injectivity. The assembly
   proof uses its supplied hypothesis h for both existence and uniqueness, then
   reflects limits from types to modules, evaluated modules to presheaves, and
   presheaves to sheaves. Read evaluationJointlyReflectsLimits and
   IsPullback.of_map_of_faithful: the former supplies naturality and the latter
   requires the reflection instances discharged by compilation. The old assembly
   proof dependency on the sectionwise node is listed under No longer needed.
   Read dag/units/sk-thm-picard-duality.json: neither helper occupies a realized
   statement or step slot, and the unit route is unchanged. Verdict: pass.
5. Compared both node JSON files against the repository. Only proof and
   proof_origin change for the sectionwise node; proof_deps also changes for
   the assembly node. The union of each proof's uses is exactly its proof_deps,
   namely lem-pc-open-module-image-section-restriction. The recorded Lean
   signatures agree with the unchanged declarations. Each recorded proof step
   matches the implemented transport or reflection argument. Verdict: pass.

Second reading changed only the proof import of
Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits to the narrower
Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits. The narrower-import scratch
copy compiled cleanly and its two axiom probes passed. No proof or node repair
was needed; two original holes closed, zero holes added, zero split off.
