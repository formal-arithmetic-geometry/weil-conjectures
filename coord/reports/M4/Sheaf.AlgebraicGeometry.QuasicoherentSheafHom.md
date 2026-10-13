## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_homObj_of_isFinitePresentation`
in `Sheaf.AlgebraicGeometry.QuasicoherentSheafHom`, without changing its signature or
public imports. Mathlib finite-presentation data supplies a covering family of specified
finite presentations. After reindexing generators and relations, the existing proved
`homObj_locally_kernel_of_local_presentation` gives a kernel between finite sums of the
restricted target. The proved coproduct and kernel closure theorems give local
quasi-coherence, which is transported to the slice site and glued by
`SheafOfModules.IsQuasicoherent.of_coversTop`.

Added proof imports `Sheaf.AlgebraicGeometry.HomLocalKernelOfPresentation` and
`Mathlib.Data.Fintype.EquivFin`. Three private helpers are fully proved: `finiteFreeIso`,
`isQuasicoherent_overEquiv_inverse`, and `isQuasicoherent_finiteBiproduct`.
The existing node's proof, proof_deps, and proof_origin follow this implementation.
Zero ranks and the empty scheme are included: coproduct closure has no nonemptiness
assumption, and the cover/gluing argument works with an empty indexing type.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_homObj_of_isFinitePresentation`
(node `lem-weil-pbc-sheaf-hom-finite-presentation-quasi-coherent`).
No holes added or split off; no sorry remains in the delivered module.
This is a proof, not a decomposition: all helpers have complete proofs and the imported
local kernel theorem is already proved.

Validation: the module compiles locally with no warnings in about nine seconds.
`#print axioms` for the target reports exactly `propext`, `Classical.choice`, and
`Quot.sound`; there is no transitive sorry dependency.

## No longer needed

Removed the proof imports `Sheaf.AlgebraicGeometry.Coherent` and
`Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum`.
The proof does not need the definition `AlgebraicGeometry.RingedSpace.IsCoherent`;
quasi-coherence uses Mathlib's existing definition and locality, so no coherent-module
theory is imported.
The binary-sum node `lem-weil-pbc-quasi-coherent-module-direct-sum` is no longer a
proof dependency. Its finite-sum induction and separate zero-rank kernel argument are
replaced by the already proved `isQuasicoherent_sigma`, recorded on
`lem-weil-pbc-quasi-coherent-module-coproduct-closure`, followed by reindexing.
Removed `pqf-def-coherent` from the proof dependencies: the proof uses Mathlib
`IsQuasicoherent.of_coversTop`, not `RingedSpace.IsCoherent`. Its statement dependency
stays unchanged, since the node cites it to describe quasi-coherence.
No claim is made that these modules are unreachable from every other project target.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The DAG's coordinate matrix argument is already packaged by
the proved `Sheaf.AlgebraicGeometry.HomLocalKernelOfPresentation`; it need not be rebuilt.
The existing node's listed binary-sum dependency was unnecessary because arbitrary
coproduct closure is already proved. Explicit types for the local open, Hom module,
and finite-index instances prevent costly elaboration and invalid field notation.
No interfaces changed and no forced adaptations or new nodes are needed.


## Second reading by M4

1. PASS. Compared the complete delivered module with the repository using a diff.
   The existing target signature is byte for byte unchanged; its docstring and all
   public imports are unchanged. Only proof imports, proved private helpers, and the
   target proof were added or removed. There are no interface changes or change records.
2. PASS. Independently compiled the module without errors or warnings (9 seconds).
   Checked the target and all three private helpers with `#print axioms` in a scratch
   copy: only `propext`, `Classical.choice`, and `Quot.sound`. No sorry or prohibited
   declaration occurs. `finiteFreeIso` constructs an isomorphism by reindexing and
   composition; it chooses no data from an unproved existence statement. The local
   presentation and kernel witnesses occur only inside the theorem proof.
3. PASS. No statements were split off and no new nodes or holes were added. Read the
   already proved local kernel theorem and the kernel and coproduct closure proofs.
   The finite-sum argument includes rank zero, the local presentation may have either
   finite index type empty, and gluing has no nonempty-cover or nonempty-scheme premise.
   A fresh grep search for quasi-coherent internal Hom and overEquiv transport found
   no direct shortcut; repository searches likewise found no replacement for this
   target. No duplicate public result is introduced.
4. PASS after metadata repair. The proof proceeds from the target through finite
   presentations, the existing local Hom kernel theorem, finite coproduct closure,
   kernel closure, and Mathlib locality. All remaining proof imports supply declarations
   used by these steps; public imports supply the signature. The only old proof
   dependencies removed are the binary-sum node and `pqf-def-coherent`, both now listed
   above. Inspected `dag/units/sk-thm-p1.json`: its realized statement and steps are
   unchanged and this below-unit reduction bypasses none of them.
5. PASS after metadata repair. The sole delivered node changes only `proof`,
   `proof_deps`, and `proof_origin`. Checked each dependency's Lean record against the
   declarations used, and checked that proof_deps is the union of step uses. Removed
   `pqf-def-coherent` from the final step and proof_deps because the proof uses Mathlib's
   locality theorem and never uses its recorded declaration `RingedSpace.IsCoherent`.
   Keeping it would incorrectly ask the import regeneration to restore `Coherent`.

Second reading changed only the node's unused coherence proof dependency and this
report. The Lean proof required no repair: one original hole closed, zero holes added,
zero split off.
