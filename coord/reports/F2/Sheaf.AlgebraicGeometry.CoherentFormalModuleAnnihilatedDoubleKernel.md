## What changed

Replaced the original sorry in
`AlgebraicGeometry.coherentFormalModule_annihilated_double_kernel` by the finite affine-cover
argument. Its signature and original docstring are unchanged. Coherence supplies
quasi-coherence of the two levels and their kernel; the affine ideal-power vanishing criterion
glues the local annihilation bounds.

The second reader proved the new local theorem
`AlgebraicGeometry.coherentFormalModule_kernel_component_affine_annihilation`, using scalar
quasi-inverses from `LinearMap.ker_coker_annihilated_mod_ideal`. Its statement now concerns one
affine open and its two local bounds, with no finite cover. The only remaining new hole is the
canonical affine projection formula for one formal module. All objects and maps in these
statements are actual categorical limits, canonical projections and kernels; no arbitrary
object is selected from an unproved existence theorem.

## Proved and sorry left

Original holes closed (1):
`AlgebraicGeometry.coherentFormalModule_annihilated_double_kernel`, node
`lem-weil-pbc-formal-systems-annihilated-by-power-kernel`.

New holes added (1):
`AlgebraicGeometry.coherentFormalModule_affine_projections`, node
`lem-weil-pbc-formal-module-affine-projections`, in
`Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineProjections`.
This has the source and a full natural-language proof in its docstring.

New auxiliary theorem proved, with no local sorry:
`AlgebraicGeometry.coherentFormalModule_kernel_component_affine_annihilation`, node
`lem-weil-pbc-formal-systems-annihilated-kernel-affine-component`.
The first worker's sorry in that new theorem has therefore been closed, rather than delivered.

This is a decomposition, not a net proof: one original hole is replaced by one strictly lower
hole about affine projections, independent of K, alpha, and the covering. Net holes closed
minus added is zero before any pruning measured by the maintainer's ledger. Both proved
annihilation statements still transitively use sorryAx through this lower theorem and existing
open dependencies. No sorry remains in the original module and no other new hole is delivered.

## No longer needed

Original direct proof dependency `lem-weil-pbc-kernel-cokernel-annihilated-mod-ideal` is replaced
in the target's proof_deps by the local component theorem and the affine-cover criterion,
together with the two quasi-coherence facts actually used. The algebra dependency is still
needed transitively and is explicitly used by the local proof; it is not globally pruned.

Removed original direct imports from the target:
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine` (used by the projection lemma instead);
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian`;
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness`;
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`;
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`;
- `Sheaf.RingTheory.AdicCompletionNoetherian`;
- `Sheaf.RingTheory.KernelCokernelAnnihilatedModIdeal` (used by the local proof instead);
- `Mathlib.Data.List.TFAE` (unused).

The second reader removed the first worker's unnecessary public imports of Scheme and
Noetherian, and restored proof-only visibility for CoherentFiniteTypeLocallyNoetherian and
QuasicoherentKernel. The new local module uses only the projection lemma, the existing scalar
lemma and the kernel-section comparison as proof imports. No whole-library module pruning is
claimed; that is determined by reachability and the pinned ledger baselines.

## Where the brief, the DAG or earlier work was wrong

The first worker's split-off statement retained all finite-cover hypotheses, while its node
had no proof steps, searches, or verbatim lean.statement. Its report also called the upper
hole proved without saying that one lower hole had replaced it. The second reading repairs
these faults and proves the local scalar argument, leaving only the affine projection
comparison. The earlier target node's single algebra dependency did not describe the actual
affine gluing step or its quasi-coherence requirements.

## New nodes

`lem-weil-pbc-formal-systems-annihilated-kernel-affine-component`: one-open annihilation bound;
proved by lifting a kernel section, applying a scalar quasi-inverse and projecting back.

`lem-weil-pbc-formal-module-affine-projections`: surjectivity and exact kernel formula for the
canonical projection of a single coherent formal module's affine section limit; remains open.
Both nodes include their source, explicit proof plan, searches and verbatim Lean signature.
No existing statement or definition changes. Import-removal record:
`coord/changes/coherentFormalModule_annihilated_double_kernel-imports.md`.

## Second reading by F2

1. Compared the delivered original module against the repository with diff and checked the
existing theorem's signature byte for byte. Only imports and the proof body change; the
existing docstring and all hypotheses/conclusions are preserved. No target or definition
changes. The other two modules and nodes are new in this delivery.
2. Compiled all three modules in import order through lcompile.py, without errors or style
warnings. Checked the sources for forbidden declarations/attributes and for sorry: exactly
one, in the named projection theorem. Axiom probes report only propext, Classical.choice,
Quot.sound and the expected sorryAx in the three declarations. There are no data definitions
or witness selections in the delivery.
3. Read Stacks 087W and 0888 at https://stacks.math.columbia.edu/tag/087W and
https://stacks.math.columbia.edu/tag/0888. The remaining projection formula is precisely the
canonical version of M/I^(n+1)M = M_n on an affine open; it is independent of annihilation.
Checked n=0 (the first quotient), I=0 (constant systems), I=top (zero systems), the zero module,
and the empty affine open. These give the expected surjections and kernels. Searched with
LeanSearch (unavailable), LeanFinder, Loogle and grep, including local Lean sources. The existing affine theorem has
the corresponding cone formula on Spec A but not the canonical formula for arbitrary affine
opens. The projection docstring explains restriction and transport between limiting cones.
The scalar argument and kernel-section injectivity use existing proved declarations.
4. The proof separates local projection comparison, the commutative-algebra scalar argument,
and global affine gluing. It retains the unit route sk-thm-p1; neither this item nor either new
helper realizes or bypasses any unit-level step, and the unit's realized fields are unchanged.
The empty finite cover is handled by the covering argument (X must be empty); no nonemptiness
assumption was added. All removed original direct dependencies/imports are listed above.
5. Checked the existing and both new nodes against the Lean. Target proof_deps names the local
bound, affine gluing and quasi-coherence facts. The local node records its actual projection
and scalar dependencies. The projection node records restriction and affine comparison. New
nodes have complete Lean records, sources, searches, creation and blueprint references.

Changed on second reading: narrowed and proved the local affine annihilation theorem;
introduced the strictly lower projection formula as the sole remaining hole; corrected import
visibility, removed unused imports, fixed compiler style warnings, completed both new nodes,
and corrected the report's hole accounting and pruning claims. Added an import-removal
change record after preflight requested it; the direct importer explicitly imports TFAE.
Compiled the unchanged direct importer against the delivered modules successfully.
The dry run passed all preflight checks (CODEX review class because of new nodes and the
public import removal).
