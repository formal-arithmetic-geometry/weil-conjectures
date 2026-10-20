## What changed

Withdrew lean/Sheaf/AlgebraicGeometry/ProjectiveLineTwistCoherentPowers.lean through
deleted.txt, as required for an item whose statement is already supplied by the adopted
source library and whose parents no longer import it. Reattached
lem-sc-p1-twist-coherent-powers to the existing proved
WeilConjectures.AlgebraicGeometry.ProjectiveLineTwistCoherentPowers declaration
AlgebraicGeometry.projectiveLine_twist_coherent_powers, recording its verbatim signature.
The source theorem drops only the unused hmul hypothesis and gives the same two families,
normalization and successor squares. No source-library file changes.

tools/downstream.py confirms zero downstream modules for the withdrawn module;
its only declaration-name occurrence is in the withdrawn file. The source module has
two direct importers: WeilConjectures and
WeilConjectures.AlgebraicGeometry.ProjectiveLineTwistMultiplication. No forced adaptations.

Change record: coord/changes/Y9-retire-projective-line-coherent-powers.md.

Validated the original module (37.9 seconds) and a scratch specialization of the source
theorem to the entire original signature (34.6 seconds, warning-free). Both the source theorem and this
specialization use only propext, Classical.choice and Quot.sound. The scratch proof records hmul as unused, then applies
exact projectiveLine_twist_coherent_powers k μ hiso. The scratch check is not delivered.

Ran msearch.py leanfinder, loogle and grep, then searched both library roots directly.
LeanFinder returned only related Proj structure-sheaf/Picard results; Loogle did not
recognize Proj.twist and the search-service grep had no hits. Direct source inspection
found the already proved source theorem, which gives the shortest route.

## Proved and sorry left

Original holes: zero. Holes closed: zero. Holes added: zero. Holes left: zero.
No split-off statements. The already proved AlgebraicGeometry.projectiveLine_twist_coherent_powers
(lem-sc-p1-twist-coherent-powers) is reused, not counted as newly proved.
This is duplicate-module pruning, not a proof or decomposition.

## No longer needed

Sheaf.AlgebraicGeometry.ProjectiveLineTwistCoherentPowers is no longer needed: no Lean
module imports it. Its duplicate positivePowers, negativePowers, negativePowers_succ,
positivePowers_square, negativePowers_square, coherentPowers, unitToTwist_one,
twistOne_invertible and public theorem are withdrawn with the module. Its two public
imports (ProjectiveSpace.Twist and Modules.Dual) disappear from this unused module only;
the source module retains both and all its definitions and proofs verbatim.
No mathematical dependency node is pruned: the same proof route still uses
def-sc-invertible-module, def-weil-pbc-proj-twisting-sheaf and lem-sc-invertible-dual.
The existing source consumer already imports
WeilConjectures.AlgebraicGeometry.ProjectiveLineTwistCoherentPowers.

## Where the brief, the DAG or earlier work was wrong

The assigned item has no sorry and compiles. Its old DAG attachment still pointed to a
Sheaf duplicate even though the current adopted source library already proves a stronger
version and all imports of this Sheaf module have disappeared. The existing proof plan
also correctly describes the source proof, so it remains unchanged. The unit route and
mathematical statement remain unchanged; only the Lean realization is reattached.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
