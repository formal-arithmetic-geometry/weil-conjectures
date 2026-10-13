## What changed

Proved the unchanged declaration `AlgebraicGeometry.affineOpenSections_resolution_quasiIso`
in `Sheaf.AlgebraicGeometry.AffineOpenSectionsResolutionQuasiIso` from the new
`AlgebraicGeometry.affineBasisSections_isIso_derivedUnit`. The original module has two proved
private helpers: `quasiCoherent_homology` and `affine_basis_vanishing`. Homology is explicitly
identified with a cokernel of a map into a kernel, so only kernel and cokernel closure are used.
The proof verifies all three acyclicity hypotheses and uses the derived-unit naturality square
with the given K-injective resolution. Exact conservative forgetting to abelian groups then
identifies native section modules with the required global-ring module complex.

Added proof-only imports of `Sheaf.AlgebraicGeometry.AffineBasisSectionsDerivedUnit`,
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`. Existing public imports, declarations,
visibility and signatures are unchanged. The new module has one named theorem, no definition
and no added public instance; its evaluation-additivity proof uses the existing additive
forgetful/evaluation composite. Updated the original DAG proof and dependencies.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.affineOpenSections_resolution_quasiIso`
(node `lem-sc-affine-open-sections-resolution-quasi-iso`). No sorry remains in the original
module. Added one hole: `AlgebraicGeometry.affineBasisSections_isIso_derivedUnit`
(node `lem-sc-affine-basis-sections-derived-unit`) in its own new module. This is a decomposition,
with one upper hole closed and one lower hole added, not a claim of net sorry reduction.
The remaining theorem isolates the unbounded affine-basis acyclicity comparison. It has no
resolution J, no morphism i and no quasi-coherence hypothesis. The original proof genuinely
proves the quasi-coherent acyclicity conditions and the subsequent naturality/scalar argument.

Both delivered modules compile through `lcompile.py --all`. No tests beyond Lean compilation
are needed for these proof edits. The delivery dry run also checks the axiom probe.

## No longer needed

The original proof does not need `lem-weil-pbc-quasi-coherent-module-cokernel-image` or its
module `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`. It uses the already proved
narrower `lem-weil-pbc-quasi-coherent-module-cokernel-closure` and kernel closure instead.
The original module needs no direct import of
`Sheaf.Algebra.Homology.KInjectiveRestrictOpen`: restriction is inside the new generic comparison,
whose node still records that dependency. Thus restriction is not claimed pruned from the whole
argument. No existing import was removed: the original file had only its two statement imports,
which remain. Temporary redundant imports of module-cohomology, right-derived K-injective
computation and Mathlib QuasiIso were tested and omitted. No whole-target-closure pruning count
is claimed; that is the maintainer's ledger calculation.

## Where the brief, the DAG or earlier work was wrong

The plan's kernel/image/cokernel discussion does not require the large image/local-surjectivity
statement: homology is a cokernel into a kernel. The similar principal-open resolution theorem
cannot be used here: its QCoh Cech comparison imports this module, creating a cycle.
The original statement and its mathematical hypotheses were preserved.

The missing substantive Lean step is the unbounded 08C2 comparison, not affine vanishing or
resolution compatibility. The new node explicitly retains term, differential-cokernel and
cohomology-sheaf vanishing on every affine basis member, with no boundedness assumption.
Checked zero F, empty V, V equal to the whole affine scheme, complexes unbounded in both
directions, and a K-injective J without quasi-coherent terms. The zero and empty cases make
both sides zero; the general argument uses no extra condition on J. Its docstring identifies
ordinary-to-derived comparison with the actual derived unit, not an arbitrary chosen iso.

Read Stacks Tag 08C2 and its linked compatible-resolution lemma Tag 071B online. The literature
mirror is absent on this remote clone; source paths identify the project's canonical documents
and the node's source records the actual public page read. LeanSearch returned HTTP 500;
recorded unavailable, with successful Loogle and Mathlib grep searches. The unit record has
empty realized lists, and no unit statement or proof route was changed.

## New nodes

`lem-sc-affine-basis-sections-derived-unit`, in
`dag/nodes/sec-picard-framework/lem-sc-affine-basis-sections-derived-unit.json`, states the
08C2 singleton-cover acyclicity criterion for the native module-valued evaluation derived unit.
Its Lean module is `Sheaf.AlgebraicGeometry.AffineBasisSectionsDerivedUnit`. Its complete proof
in words follows good truncations, the compatible resolution tower of 071B, eventual section
cohomology stabilization and the Mittag-Leffler limit calculation, with open restriction and
scalar forgetting identifying the derived unit. It is strictly a part of the original argument.
There are no interface changes to existing modules and no change records or forced adaptations.

## Second reading by G2

1. Compared the delivered item module with the repository version. The theorem signature and
   existing declarations are unchanged; only proof imports, helper proofs, and the target proof
   body changed. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; there are no errors, forbidden
   declarations, or unexpected `sorry`s. The sole remaining `sorry` is the named split theorem
   `affineBasisSections_isIso_derivedUnit`. Verdict: pass.
3. Checked the split node and its docstring against the 08C2 singleton-cover criterion. It is a
   strictly smaller comparison statement, with the required source, proof steps, and Lean record;
   no duplicate library declaration was found. Verdict: pass.
4. The proof uses the shorter kernel/cokernel route and the new derived-unit comparison, and the
   DAG proof dependencies match those uses. The original image/local-surjectivity dependency is
   pruned while the unit route remains unchanged. Verdict: pass.
5. The node statement, proof, proof dependencies, and proof origin agree with the Lean files; the
   unit record needs no change. Verdict: pass.

Changed only this report section after the review; no Lean or DAG repairs were needed.
