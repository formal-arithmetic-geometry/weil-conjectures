## What changed

Repaired the returned duplicate-declaration failure. The proved affine bridge
`AlgebraicGeometry.finite_sections_of_formalQuotient_and_torsionKernel` now lives in
`Sheaf.AlgebraicGeometry.CoherentOfFormalQuotientsAndTorsionKernel`, beside the existing
private `exists_fg_lift` and `finite_of_quotient_and_torsion_kernel` lemmas. Their original
statements, visibility and proofs are retained verbatim and reused once. The unlanded
`CoherentOfFormalQuotientsAndTorsionKernelAffine.lean` file was removed from the sandbox;
it does not exist in the shared repository, so no landed-module withdrawal is necessary.
The bridge node is retained and its Lean attachment now names the assigned module.

The coherence theorem applies the bridge on the singleton top affine cover, then uses the
affine finite-type and Noetherian coherence criteria. Its signature is unchanged.
The private ideal-power/range lemmas now come from a proof-only `import all` of the
upstream `WeilConjectures` module, and the cokernel API is imported explicitly.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.coherent_of_formalQuotients_and_torsionKernel`
(node `lem-weil-pbc-coherent-of-formal-quotients-torsion-kernel`).
The added affine-sections theorem is fully proved. Zero holes added, zero holes remaining
in the delivered module, and no statements split off with `sorry`.

## No longer needed

Removed the proposed sibling module and its import
`Sheaf.AlgebraicGeometry.CoherentOfFormalQuotientsAndTorsionKernelAffine` from this delivery.
Removed its duplicate copies of `exists_fg_lift` and
`finite_of_quotient_and_torsion_kernel`; the originals remain in the assigned module.
Replaced `import all Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
with a proof-only direct import of
`WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`.
The retired Sheaf wrapper does not expose the upstream private range lemmas.
All other original imports are used by the proof. No DAG dependency nodes are pruned:
the bridge now records the full kernel, tensor, quotient, ideal-product, and coherence
APIs it uses, while the final step retains the unit route through affine finite type.

## Where the brief, the DAG or earlier work was wrong

The returned delivery copied two existing private theorems into a new module. Its earlier
second reading missed these duplicates. The repair keeps the bridge in their existing
module, so its proof uses those declarations directly and no import cycle is introduced.
The retained proof also needed import updates after the upstream synchronization: the
Sheaf wrapper no longer exposes private `powers_range` and `multiplication_range`, and
`isQuasicoherent_cokernel` requires the explicit upstream cokernel import.

## New nodes

`new-stage3-coherent-formal-quotients-affine-sections` records the fully proved finite-sections
bridge. It is retained from the returned delivery, with its Lean attachment corrected to
`lean/Sheaf/AlgebraicGeometry/CoherentOfFormalQuotientsAndTorsionKernel.lean`.
No existing declaration changes signature or visibility, and no consumer adaptations are
needed. No change record for an existing definition or statement is required.

## Second reading by F2

1. Compared the delivered module with the repository version. Existing declaration
   signatures and visibility are unchanged; the only interface addition is the
   new affine-sections theorem and its recorded node. The coherence target statement
   is unchanged.
2. Compiled the module with `lcompile.py` and checked both theorem declarations with
   `#print axioms`; they use only `propext`, `Classical.choice`, and `Quot.sound`.
   There are no `sorry`, axioms, unsafe declarations, or hollow definitions.
3. Checked the added affine-sections statement against the affine finite-generator
   argument and its cited declarations. It is strictly the affine component needed
   by the target, with no extra hypothesis or weakened conclusion; searches found no
   existing theorem duplicating it.
4. Checked the proof route and imports. The proof reuses the existing private
   generator lemmas, keeps the unit route through affine finite type and coherence,
   and removes the duplicate sibling module/import. The DAG proof and dependency
   records match the declarations used.
5. Checked the unit record and node attachments: the target remains realized by the
   affine bridge followed by the finite-type criterion, and the new node records its
   source, proof, dependencies, and Lean declaration consistently.

No further changes were needed in this second reading.
