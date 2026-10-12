## What changed

Proved `AlgebraicGeometry.Scheme.schemeDerivedQCohProperty_of_isPseudoCoherent_degree`
in `Sheaf.AlgebraicGeometry.PseudoCoherentQCohDegree`, preserving its signature and
public import. Added the proof-only import
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`, which supplies
both kernel and cokernel closure and quasi-coherence of free sheaves.

Three proved private helpers carry the local argument: `qc_over_inverse` transports
quasi-coherence back from an open subscheme to the localized site; `qc_homology`
expresses homology as the cokernel of a morphism into a kernel; and
`qc_local_free_homology` applies this to the finite-free model. The main proof chooses
the neighbourhoods, identifies restricted derived homology with model homology,
and applies quasi-coherence locality on this covering family.

The node's proof, proof dependencies, and proof origin now record this implementation.
The unit `sk-thm-picard-duality` has no realized statement or steps naming this node;
its route is unchanged. No definitions, public interfaces, or other modules changed.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.schemeDerivedQCohProperty_of_isPseudoCoherent_degree`
(node `lem-sc-pseudo-coherent-qcoh-degree`). All three private helpers are proved.
Holes closed: 1. Holes added: 0. Sorries left in the delivery: none.

Local compilation succeeds. `#print axioms` for the public theorem lists exactly
`propext`, `Classical.choice`, and `Quot.sound`; thus no imported sorry remains in
its proof. The import-direction check accepts the source-library import.

Searches used `msearch.py` leanfinder for homology of quasi-coherent sheaves,
loogle for `SheafOfModules.IsQuasicoherent`, and grep for homology/quasi-coherence,
plus source searches in both library roots and Mathlib. No existing complete
pseudo-coherent degreewise result was found. Existing kernel/cokernel and
site/derived-category transport results suffice without new statements.

## No longer needed

No existing import was removed: the original module had only its necessary public
`PseudoCoherentComplex` import. Removed `pqf-def-coherent` from this node's
proof dependencies: coherent sheaves and finite presentation are unnecessary.
`Sheaf.AlgebraicGeometry.Coherent` is not needed by this proof. The item's
statement-dependency record is unchanged. Replaced the planned
`lem-weil-pbc-quasi-coherent-module-cokernel-image` dependency by the narrower existing
`lem-weil-pbc-quasi-coherent-module-cokernel-closure`, whose Lean record is the proved
source lemma `Scheme.Modules.isQuasicoherent_cokernel`. The larger wrapper module
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage` is not imported.
No image calculation, boundedness argument, or affine pseudo-coherence machinery
is needed. Kernel and cokernel closure remain genuine proof dependencies.
These are local pruning claims, not claims that the modules leave all targets' closures.

## Where the brief, the DAG or earlier work was wrong

The proof plan is mathematically valid. Its coherent-sheaf definition dependency
was unnecessary. The bounded-above hypothesis supplied by pseudo-coherence is not
needed for quasi-coherence of an individual homology sheaf: termwise
quasi-coherence suffices for the kernel/cokernel argument.

The original docstring calls Tag 08E5 Lemma 36.13.5. The current
[Stacks Tag 08E5](https://stacks.math.columbia.edu/tag/08E5) is numbered 36.10.1
and proves the quasi-coherent cohomology assertion by local perfect models.
The stable tag and mathematical argument agree; the existing docstring is preserved.

The argument also handles an empty scheme (the point-indexed cover is empty and
covers the empty space), rank zero free terms, and every integer degree. Neither
Noetherianity nor affineness nor a uniform bound/rank is assumed.

## Second reading by X3

1. **Interface unchanged — PASS.** Compared the delivered module with the repository
   using `diff -u` and checked the existing theorem signature byte for byte. Its
   hypotheses, conclusion, visibility, public import, and existing docstring are
   unchanged. The only additions are three proved private helpers, a private
   proof import, and declaration-scoped elaboration options. No definitions or
   target statements changed; no change record is needed.
2. **Kernel-checked proof — PASS.** Compiled the delivered module with
   `lcompile.py` successfully (13.6 seconds, no warnings). Compiled a scratch
   copy with `#print axioms` for the public theorem and all three helpers:
   each uses only `propext`, `Classical.choice`, and `Quot.sound`. There are
   no sorries, forbidden declarations, or data definitions in the delivery.
   The neighbourhoods and models are chosen from the input hypothesis `hE`,
   not from an unproved existence theorem.
3. **Split-off statements — PASS (none).** No public statements or holes were
   added. Read each private helper: inverse site equivalence preserves local
   presentations; homology is the cokernel of the incoming map into the outgoing
   kernel; finite-free terms are quasi-coherent after the open-site equivalence.
   These arguments hold for rank zero, zero differentials, empty opens/schemes,
   and every integer degree. No boundedness or Noetherianity assumption is needed.
4. **Route and pruning — PASS.** Independently searched the library and Mathlib
   for quasi-coherent homology, including `msearch.py grep` with
   `IsQuasicoherent.*homology|homology.*IsQuasicoherent`, and inspected the
   upstream kernel/cokernel results. A similar argument in
   `SupportedPerfectDetectorAffineConstruction` is private and unavailable;
   it supplies no shorter public theorem. Both imports are necessary, and the
   added cokernel import is correctly proof-only. The report accounts for both
   old dependencies no longer used: `pqf-def-coherent` and
   `lem-weil-pbc-quasi-coherent-module-cokernel-image`. The latter is replaced
   by the narrower existing cokernel-closure node. The unit's `realized` fields
   do not name this node, and its route is preserved.
5. **DAG agrees — PASS.** Read the old and new item nodes and the kernel and
   cokernel dependency nodes. Only `proof`, `proof_deps`, and `proof_origin`
   changed. The union of the proof steps' `uses` equals `proof_deps` exactly;
   the recorded declarations are the ones used in Lean. The three steps
   accurately describe the local models, homology calculation, and covering
   descent. There are no new node files or changed statements.

Second reading changed only this report: clarified that the item's statement
dependencies stay unchanged and added the independent review evidence. The Lean
proof and DAG edits were retained as written. Holes closed: 1; holes added: 0;
no split-off statements and no removed import modules.
