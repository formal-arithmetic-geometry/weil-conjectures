## What changed

Repaired and proved the intended finite-submodule gluing theorem in
`Sheaf.AlgebraicGeometry.HilbertEmbeddedPointsGluing`. The old Lean statement was
false: arbitrary `Nloc` values were unrelated to localization or restriction, and
the conclusion even prescribed them outside the charts. The replacement uses the
concrete `affineSectionSubmodule`, the abelian image of a finite free map constructed
from generators of the given section submodule. Compatibility is required only on
opens principal in both affine charts, exactly as in the mathematical node.

The proof realizes the local images, passes from common principal opens to all
overlap opens by sheaf separation, constructs overlap isomorphisms by kernel-of-cokernel
factorization, verifies the cocycle by cancellation, glues sheaves and maps, proves
coherence and the affine cokernel formula, and proves uniqueness by local section
ranges. All helper theorems are proved. The construction contains no sorry or
arbitrary data selected from an unproved existence assertion.

The node's mathematical statement stays unchanged. Its Lean attachment and proof
route are updated. The definition and theorem belong to that existing node; no new
node or source-library change is needed. The change record is
`coord/changes/V7-hilbert-embedded-points-localization.md`.

## Proved and sorry left

The original module had one hole, in
`AlgebraicGeometry.Scheme.Modules.existsUnique_coherent_submodule_of_affine_cover`.
Its invalid signature is repaired, and the corrected theorem is proved in full.
This is a statement repair with a complete replacement proof, not a proof of the
false old assertion. There are zero sorry declarations left and zero holes added;
no result is split off. Every private helper and the concrete image definition are
complete.

The final principal-overlap module compiled cleanly in 57.1 seconds through
`lcompile.py`, with no warnings. Its gluing diagnostic also compiled in 28.3 seconds.
The delivery command performs the axiom and server preflight checks.
The nested restriction evaluation equation is proved once and used by rewriting,
avoiding repeated expensive unfolding of the overlap functors.

## No longer needed

Removed the obsolete import `Sheaf.Topology.GlueSheavesOfModules`, whose adopted
replacement `WeilConjectures.Topology.GlueSheavesOfModules` supplies the gluing theorem.
Removed the direct import `WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`:
coherence follows from the existing quasi-coherent-submodule criterion, so the main
proof does not separately redo finite-type descent.

The reviewer removed the unused imports `Cohomology.Affine.CechAcyclic`,
`Modules.QuasicoherentKernel` and `Modules.QuasicoherentCokernel` under
`WeilConjectures.AlgebraicGeometry`: the module compiles without them (lcompile, 47.4 s).

The direct proof route no longer invokes
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-spec-module-tilde-sections`,
`lem-weil-pbc-quasi-coherent-finite-type-affine`, or
`lem-weil-pbc-module-restriction-open-immersion-colimits`. Finite free images and the
existing affine cokernel theorem replace those direct steps. These nodes may remain
transitive dependencies of the proved library tools; no global withdrawal is claimed.
`pqf-def-locnoeth` stays a statement dependency, rather than a separate proof step.
The common-principal-open node stays and is used to refine an arbitrary overlap open.

During this session the independently landed T1 proof of RemoveEmbeddedPoints changed
to `lem-sc-canonical-embedded-points-gluing`. The current DAG has no parent citing
this item and `tools/downstream.py` reports zero importers. The delivery does not
claim a net reduction of holes in the current target closure. It retains and repairs
the assigned library statement; it does not revert or alter that concurrent parent
proof, withdraw adopted source declarations, or claim its independent pruning.

## Where the brief, the DAG or earlier work was wrong

The DAG states an actual localization theorem; its old Lean encoding instead
quantified over arbitrary `Nloc`. For a singleton affine cover X, take N = 0,
Nloc X = 0 and Nloc V = all sections on a nonempty proper open V. The old compatibility
condition is tautological, but no quasi-coherent subobject with zero affine section
image can realize that nonzero value on V. This demonstrates the missing localization
condition independently of the additional error of prescribing values outside U_i.
The repaired statement uses a real affine sheaf image, not an extra existence
hypothesis or repackaging of the desired global conclusion.

The concrete image has affine section range N_i. Quasi-coherent affine localization
then identifies its range on D(f) with the image of (N_i)_f in F(D(f)); this explains
why the public compatibility condition is precisely the node's localized-submodule
condition. Common principal opens form a basis of each overlap; the proof establishes
that refinement and uses sheaf separation to extend the agreement. Empty charts,
an empty scheme or cover, and the zero submodule need no nonemptiness or nonzero-rank
assumption: finite free rank zero, categorical images, and cover separation cover
these cases.

No current consumer uses the old declaration, and all six target declarations are
unchanged. No adaptation of another group's module was needed.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
