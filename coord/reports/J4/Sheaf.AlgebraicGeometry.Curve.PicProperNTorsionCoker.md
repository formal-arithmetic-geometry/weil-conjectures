## What changed

Corrected the Lean record of `lem-sc-pic-proper-ntorsion-coker` to name the actual
`AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker` declaration and its exact
signature. Added the copyright header and module docstring to
`Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker`.
The existing theorem signature, complete proof, visibility and imports are unchanged.
The node's existing proof plan already describes that proof and is retained.

## Proved and sorry left

The supplied module already proves
`AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker`
(node `lem-sc-pic-proper-ntorsion-coker`) without a direct `sorry`.
It compiled unchanged using lcompile.py. Holes closed: zero of zero.
Holes added or split off: zero. No `sorry` is left in any delivered module.
This is a repair of a stale declaration record, not new proof progress.
The proof still uses the library's degree splitting and degree-zero divisibility;
no claim is made that all their transitive proof dependencies are closed.
The kernel calculation works for n = 1. The stated nonzero-cast hypothesis excludes
n = 0, and excludes integers divisible by the positive characteristic.

## No longer needed

None. The private Curve.Picard import supplies the degree splitting and kernel
identification, and PicProperNTorsionDiv supplies divisibility. Both remain necessary.
No node, module or import has been pruned.

## Where the brief, the DAG or earlier work was wrong

The brief says this module still contains `sorry`, but its supplied version has a
complete compiling proof, previously landed by K2. coord/repairs.txt instead lists
it for the duplicate notice in upstream review #1428.

The cited replacement `Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient`
and its cited module `WeilConjectures.AlgebraicGeometry.Curve.Jacobian` are absent
from the project's adopted source library, the supplied read-only slopmaster2
checkout, and the weil-lean source snapshot. Searches of all three source trees
found neither declaration. The available Jacobian module is Picard.Jacobian,
which supplies Jacobian representability but not that bundled theorem.
Curve.Estimate obtains this cokernel through `f.pic_proper_ntorsion`; its H2
calculation therefore cannot serve as an independent replacement either.
Deleting this theorem and repointing its caller to the cited absent declaration
would break the library. The duplicate-removal request remains inapplicable to
this snapshot and needs the replacement theorem supplied before it can be acted on.
No replacement theorem was fabricated, and no unheld caller was changed.

The node's Lean record incorrectly used that absent replacement name while its
module, file and proof plan described the existing Hom.pic_proper_ntorsion_coker.
This delivery corrects the record to agree with the actual Lean statement without
altering the mathematical statement or the unit route. The unit sk-thm-curveestimate
has no fixed realized proof steps bypassed by this repair.

## Earlier second reading (a previous round; superseded)

1. **Statement integrity.** Compared the delivered Lean module with the repository version. The theorem signature is byte-for-byte unchanged; only the module header/docstring and the node's stale declaration record differ. Verdict: pass.
2. **Proof validity.** Compiled the module with `lcompile.py`; it has no `sorry`, axiom, unsafe, opaque, extern, or implemented_by declarations. The proof follows the stated Picard splitting, divisibility, kernel, and first-isomorphism route. Verdict: pass.
3. **Split statements.** No new theorem or split-off hole was introduced. The corrected DAG declaration names the theorem actually present in Lean, and its statement matches exactly. Verdict: pass.
4. **Pruning and imports.** Checked the proof dependencies and imports. Both `Curve.Picard` and `PicProperNTorsionDiv` are used, and no import or dependency can be removed. The unit route remains the direct Picard decomposition plus degree-zero divisibility. Verdict: pass.
5. **DAG agreement.** The node's `lean.declaration` and `lean.statement` now agree with the compiled theorem; proof steps and `proof_deps` remain accurate. Verdict: pass.

Changed the stale node declaration record and added the module header/docstring. No proofs, theorem statements, imports, or holes were changed.

## Second reading by J4

1. **Statement integrity.** Compared the delivered Lean module with the repository version. The theorem signature is byte-for-byte unchanged; only the module header/docstring and the corrected DAG declaration record differ. Verdict: pass.
2. **Proof validity.** Compiled the module with `lcompile.py`; it has no `sorry`, axiom, unsafe, opaque, extern, or implemented_by declarations. The kernel proof uses the Picard decomposition, degree-zero divisibility, and the first-isomorphism construction. Verdict: pass.
3. **Split statements.** No new theorem or split-off hole was introduced. The DAG declaration and Lean declaration agree exactly. Verdict: pass.
4. **Pruning and imports.** Both `Curve.Picard`/`PicardDecomposition` and `PicProperNTorsionDiv` are needed by the proof. The decomposition node is retained in `proof_deps`; no import or dependency is pruned. The unit route is preserved. Verdict: pass.
5. **DAG agreement.** The node's declaration, statement, proof steps, and `proof_deps` now match the compiled Lean proof. Verdict: pass.

Changed the stale node declaration record and restored the decomposition proof dependency; added the required second-reading record. No theorem statements, definitions, imports, or holes were changed.
