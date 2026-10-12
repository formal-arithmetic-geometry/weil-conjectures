## What changed

The signature of AlgebraicGeometry.grothendieckDevissage_recoverLevels is unchanged.
Its proof now compiles without a local hole. A proved private helper,
torsionTriple_comparison_iso, compares two supplied torsion-controlled triples using
GrothendieckExistenceEasyTorsionTriple: compare each with its selected triple, compose
one comparison inverse with the other, and cancel to recover the specified completed
comparison. The main proof applies this helper at each positive level and proves every
transition identity from naturality and detection of maps by completion and a
power-torsion-kernel comparison.

Three new modules isolate genuinely smaller steps: quotient-theoretic completed
comparison (no torsion assumptions), reduction of any coherent map's actual torsion
bound, and detection of coherent maps by completion plus a reference map whose kernel
is power-torsion. The existing recovery node now records the implemented route. No
definition, public signature, target, or other existing module is changed.

All four delivery modules compile in import order through lcompile.py. The existing
torsion-triple dependency was initially absent from the local compiled library; it
became available after the regular refresh. The scratch attempts are outside the
delivery's lean/ tree and are not part of the delivery.

## Proved and sorry left

Closed: AlgebraicGeometry.grothendieckDevissage_recoverLevels
(lem-weil-pbc-devissage-recover-levels), the sole original sorry. The private helper
AlgebraicGeometry.torsionTriple_comparison_iso has a complete proof.

Added and still sorry:

- AlgebraicGeometry.coherentMap_reduction_torsion
  (lem-weil-pbc-coherent-map-reduction-torsion).
- AlgebraicGeometry.coherentMap_torsion_completion_ext
  (lem-weil-pbc-coherent-map-torsion-completion-ext).
- AlgebraicGeometry.grothendieckDevissage_completedComparison
  (lem-weil-pbc-devissage-completed-comparison).

This is a decomposition: one original hole closed and three new holes added, net -2
before any separate closure-pruning effects. It is not an unconditional proof. The
existing imported AlgebraicGeometry.grothendieckExistenceEasy_torsionTriple remains
open and is used directly, not duplicated. Each new hole has its own source, full
natural-language proof and DAG node. No hole is inside a definition or private helper.

## No longer needed

Removed direct proof imports from GrothendieckDevissageRecoverLevels:

- Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated, now used by the separate
  coherent-map reduction step rather than directly by the assembly.
- Sheaf.RingTheory.FormalGlueingComplexExact
  (lem-weil-pbc-formal-glueing-complex-exact).
- Sheaf.Topology.GlueSheavesOfModules
  (lem-weil-pbc-glue-sheaves-of-modules).

The transition argument no longer needs general formal gluing or gluing of sheaves:
its difference has image in a bounded-torsion kernel and is detected by completion.
Those two nodes are removed from the recovery node's direct proof dependencies.
The annihilation node remains needed by the new reduction node. Formal gluing and
sheaf gluing are still reached by the imported torsion-triple theorem, so no claim is
made that their modules disappear from the entire targets' import closure. No unit
statement or realized unit step is bypassed. All remaining imports serve statements
or an explicitly identified proof step; no additional direct import is removable.

## Where the brief, the DAG or earlier work was wrong

The existing torsion-triple uniqueness statement is sufficient for levelwise recovery,
but the listed dependencies do not themselves supply a coherent-sheaf reduction bound
for an actual map or the quotient-interchange comparison interface. These are isolated
as new statements instead of assuming an unavailable interface or unrestricted
faithfulness of completion.

The original transition plan used a stronger general formal-gluing argument than
needed: once the two comparisons to H agree, their difference lands in a kernel killed
by a fixed ideal power. Completion is faithful on that particular kernel. This is valid
also for the unit ideal (the kernel is already zero), the zero ideal (completion is the
identity), and the empty scheme. Reduction modulo the unit ideal gives zero modules;
modulo the zero ideal gives the original map, whose bound by K^t implies the weaker
K^(2t) bound. At every positive n, iterated quotients are both quotients by the sum of
the two ideal products; this remains true for zero and unit ideals. No new statement
is a restatement of recovery: completed comparison alone can lose components away from
V(K), reduction torsion asserts no isomorphism, and map detection asserts only equality
of two already supplied maps.

An attempted proof of the detection lemma from FormalCompletionExact encountered its
non-definitionally-equal native and abelian zero-morphism structures. That attempt is
kept in scratchpad; the delivered statement uses the finite-module affine argument
instead. No interface adaptation or rule workaround was performed.

The source tex files are absent in this local mirror. The cited Stacks text was read
from the public pages for Tags 088A, 0889 and 0888. The blueprint ancestor helper returned
None for this recently created item's module-valued created.item; the existing node's
explicit blueprint.from was followed instead, retaining thm-weil-pbc-finite-etale-lifting
as ancestor and inserting the recovery node in the via chain. LeanSearch returned
Internal Server Error and is recorded as unavailable; LeanFinder, Loogle and grep ran.

## New nodes

lem-weil-pbc-devissage-completed-comparison, in
Sheaf.AlgebraicGeometry.GrothendieckDevissageCompletedComparison, is only the completed
comparison and its naturality, before using any torsion or algebraization uniqueness.
Source: Stacks Tag 088A, final paragraph. Its proof constructs quotient interchange by
universal cokernel properties, transports beta inverse through sigma, and checks the
comparison equation using htheta and hsquare.

lem-weil-pbc-coherent-map-reduction-torsion, in
Sheaf.AlgebraicGeometry.CoherentMapReductionTorsion, specializes the commutative algebra
fact of Remark 0888 to actual coherent maps on all affine opens. The same statement is
used twice: reduction of a in I, and K-completion of each alpha_n. It retains the exact
uniform exponent 2t rather than asserting preservation of t.

lem-weil-pbc-coherent-map-torsion-completion-ext, in
Sheaf.AlgebraicGeometry.CoherentMapTorsionCompletionExt, states injectivity for maps
with the same completion and comparison to a map having bounded-torsion kernel. Source:
Tag 0889 uniqueness and Tag 088A transition compatibility. It requires no cokernel bound
and reduces on affines to injectivity of completed inclusions and stabilization of
bounded-torsion modules. Mathlib's AdicCompletion.map_injective provides the ring-level
injectivity, not the sheaf statement. Three kinds of searches are recorded for all new
nodes. No change record is needed because no existing interface changed.

## Second reading by E3

1. Compared the delivered recovery module with the repository version. The public
statement of `grothendieckDevissage_recoverLevels` is byte-for-byte unchanged; only
proof text, private helpers, and proof-only imports changed. Verdict: pass.
2. Compiled all four delivered modules with `lcompile.py --all`; compilation succeeds
without errors. The recovery hole is closed, and the only remaining holes are the
three named split-off theorems, each with a docstring, node, and no hole in a
definition. Verdict: pass.
3. Checked the three split-off statements against their uses and edge cases recorded
above; each is strictly smaller than recovery and no duplicate library theorem was
found by repository search and the recorded searches. Verdict: pass.
4. The proof follows the shorter quotient-comparison, torsion-reduction, and bounded
kernel completion-detection route. Removed formal-gluing and sheaf-gluing imports
are listed under `No longer needed`; the unit route and realized steps remain. Verdict:
pass.
5. Updated the recovery node's proof, proof dependencies, and proof origin to match
the Lean proof; each new node records its statement, dependencies, source, and Lean
declaration. Verdict: pass.

Changed during second reading: added this review record only. No Lean statement,
definition, or proof was changed after the first reading.
