## What changed

Proved `Algebra.TensorProduct.purelyInseparable_baseChange_residue` in
`Sheaf.RingTheory.PurelyInseparableBaseChangeResidue`, preserving its signature and visibility.
Added the proof-only Mathlib import `RingTheory.Spectrum.Prime.Homeomorph`.
The second reading removed four redundant added imports (listed below).
Updated the item's DAG proof, proof dependencies, and proof origin to match the Lean proof.

Contraction of maximal ideals in the finite algebra and injectivity of contraction from the
purely inseparable spectrum homeomorphism give locality and the unique prime over the closed
point. An explicit quotient lift constructs the residue map. Finiteness descends from its
A-module structure along the proved scalar tower. Mathlib's direct quotient-tensor equivalence
and a linear equivalence for exactly the stipulated transported K-action prove the fibre formula
and rank equality. No additional theorem or definition was introduced.

## Proved and sorry left

Closed the sole original hole:
`Algebra.TensorProduct.purelyInseparable_baseChange_residue`
(node `lem-weil-pbc-purely-inseparable-base-change-residue`).
There are no sorries left in the module and no holes added elsewhere. This is a full proof,
not a decomposition. The module compiles without warnings using `lcompile.py`.

## No longer needed

Removed no repository imports. Removed four redundant imports added by the first worker:
`Mathlib.RingTheory.TensorProduct.Quotient`, `Mathlib.RingTheory.TensorProduct.Finite`,
`Mathlib.RingTheory.Ideal.GoingUp`, and `Mathlib.LinearAlgebra.Dimension.Constructions`.
The retained imports already expose their required declarations; removing all four together
still compiles. The sole newly added import is proof-only and necessary.
The proof no longer uses `lem-weil-pbc-tensor-cancel-base-change`: the direct Mathlib
`Algebra.TensorProduct.quotientTensorEquiv` already gives the needed isomorphism and pure-tensor
formula. That node is a Mathlib leaf, so there is no associated Sheaf module to remove.
No other planned dependency is pruned: finite-algebra contraction, rank-preserving base change,
and the quotient-base-change identity are still used. No unit statement or realized step is
bypassed. The nilradical construction and the separate quotient/swap/cancellation chain in the
old plan are unnecessary; the existing Mathlib spectrum homeomorphism supplies prime uniqueness.
No whole-library claim of unreachability is made for nodes used by other modules.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The plan was longer than needed:
Mathlib already provides `quotientTensorEquiv` directly, and the purely inseparable spectrum
homeomorphism avoids constructing and transporting the nilradical. The residue finiteness clause
follows from `Module.Finite.of_restrictScalars_finite`, using the explicit scalar-tower formula,
without transporting a finite basis to a further quotient. No signature or public import changed.

## Second reading by V2

1. **Unchanged interface: pass.** Compared the delivered Lean module and JSON node with
   the repository using `diff -u`. The sole existing theorem's complete signature, universe
   parameters, hypotheses, visibility, and conclusion are byte for byte unchanged. All original
   public imports remain. The node changes only `proof`, `proof_deps`, and `proof_origin`.
   No definitions, other modules, or change records are delivered.

2. **Proof and axioms: pass.** Compiled the module with `lcompile.py` without errors or
   warnings. A scratch copy containing `#print axioms
   Algebra.TensorProduct.purelyInseparable_baseChange_residue` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`; there is no `sorryAx`. There are no sorries or forbidden
   declarations in the delivered Lean. The quotient map is explicitly constructed with
   `Ideal.Quotient.lift`; no arbitrary data is extracted from an unproved existence theorem.
   Read Stacks Tag [07E5](https://stacks.math.columbia.edu/tag/07E5), proof of (3) => (1),
   and the Mathlib implementations of the spectrum homeomorphism, quotient-tensor equivalence,
   finite-module scalar restriction, and rank formula. The source asserts locality and finite
   flatness; this lemma proves the stated expanded residue and fibre properties. Characteristic
   zero and the identity extension are covered by the same purely inseparable theorem.

3. **Split statements: pass, none.** No new declaration, split-off hole, or node was added.
   Checked the existing library for the theorem name and for purely inseparable local/residue
   results; no single shorter declaration supplies this conjunction. With A a field the prime
   argument still applies (m = 0); no assumption that the tensor product is reduced or a field
   enters the proof. The possibly nonreduced closed fibre is handled by the spectrum theorem.

4. **Route and pruning: pass after import repair.** The prime-spectrum theorem gives
   injectivity of contraction; integrality of the finite A-algebra gives maximal contraction.
   Together these prove locality and the unique prime containing mB. The residue formula gives
   exactly the scalar tower needed for finiteness. The explicit linear equivalence uses exactly
   the K-action stipulated by the unchanged statement, so `finrank_baseChange` applies.
   Read `dag/units/sk-thm-p1.json`, including every `realized` entry: neither this supporting
   lemma nor the removed cancellation dependency realizes a unit step; all realized nodes and
   the unit route remain. The complete old-minus-new `proof_deps` is just
   `lem-weil-pbc-tensor-cancel-base-change`, recorded above. Tested removal of every new import
   individually and then the four redundant imports together; the latter compile cleanly.
   Removing `Spectrum.Prime.Homeomorph` fails with the expected unknown theorem.

5. **DAG agreement: pass.** Read all three retained dependency nodes. The finite-algebra
   local-radical node supplies maximal contraction; the quotient-base-change node supplies the
   quotient identity, now via Mathlib's direct `quotientTensorEquiv`; the free-base-change node
   supplies rank preservation, implemented by `Module.finrank_baseChange`. The three updated
   steps match the Lean construction, and `proof_deps` is their union. `proof_origin` names the
   Mathlib declarations actually used, including the direct spectrum theorem (Tag 0BRA).

**Changed by this reading:** removed the four redundant proof-only imports listed under
`No longer needed`, corrected the report's import claims, and appended this review. The proof
body, signature, and node supplied by the first worker needed no mathematical repair.
