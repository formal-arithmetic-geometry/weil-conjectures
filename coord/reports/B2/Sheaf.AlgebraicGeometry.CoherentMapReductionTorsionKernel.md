## What changed

Proved `AlgebraicGeometry.coherentMap_reduction_torsion_kernel` in
`Sheaf.AlgebraicGeometry.CoherentMapReductionTorsionKernel`, with its existing signature.
The proof follows Stacks Remark 0888: affine scalar quasi-inverses preserve the ideal
multiples that are kernels of quotient projections, so products of two scalars in K^t
kill reduced-kernel sections. The affine-cover criterion gives global vanishing.

Added proof-only imports of CoherentFiniteTypeLocallyNoetherian,
Modules.IdealTimesQuasiCoherentAffineSections, Modules.QuasiCoherentCokernelImage,
QuasiCoherentTensorProductAffineSections, IdealPowerProductZeroAffineCover,
RingTheory.KernelCokernelAnnihilatedModIdeal, and the source module
WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel.
The private helpers `power_multiplication_range` and `quotient_affine` are proved;
they implement existing DAG facts about products, tensor sections, images, and quotients.
Updated the existing node's proof, proof_deps, and proof_origin to record these uses.
The unit route is unchanged. No other module or public interface is changed.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.coherentMap_reduction_torsion_kernel`
(node `lem-weil-pbc-coherent-map-reduction-torsion-kernel`).
No holes remain in the item. No new holes or split-off statements were added.
The proof and both private helpers compile without warnings.

## No longer needed

None. All four original proof dependencies are used, and the original public import
is needed by the statement. No existing import, node, or module is pruned.
An unnecessary direct proof import of
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` was removed during development;
its kernel-section primitives are already publicly available through the required imports.
No formal-limit, completion-projection, or formal-system annihilation modules are imported.

## Where the brief, the DAG or earlier work was wrong

The original plan is correct. Its affine quotient step required explicit glue:
the existing ideal-times-affine theorem exposes product ranges for the first power and
inclusion ranges for every power, so the proof computes multiplication by a general
power using the affine tensor-section comparison and the cokernel-image theorem.
There is no change to a statement or definition and no forced adaptation.


## Second reading by B2

1. Compared the delivered module and node against the read-only repository. PASS:
   the sole existing theorem signature is byte-for-byte unchanged, including every
   hypothesis, the exponent `2 * t`, and all quotient levels `n + 1`. The public import,
   visibility, and definitions are unchanged. Only this module and its existing node
   are delivered; no change record is needed.
2. Compiled the module locally through `lcompile.py`. PASS: no errors or warnings,
   no remaining `sorry`, no definitions added, and no forbidden declarations or
   attributes. A scratch copy with `#print axioms` for the theorem and both private
   helpers reports exactly `propext`, `Classical.choice`, and `Quot.sound` for each;
   no `sorryAx` remains even through their dependencies. The scalar quasi-inverse
   comes from a proved theorem and is used only inside a proof, not to define data.
3. PASS: no new holes, public statements, or split-off nodes. Read both private helper
   proofs: tensor generation computes the range, and affine exactness computes the
   quotient kernel. These handle zero ideals, the unit ideal, zero modules, empty
   affine opens and the empty scheme; the positive-power hypothesis is available
   even at `n = 0` because the reduction exponent is `n + 1`. Searched independently
   with LeanFinder for "sections of quotient quasi coherent sheaf by power of ideal
   kernel projection", Loogle for `Submodule.smul_top_le_comap_smul_top`, and `rg`
   for quotient quasi-coherence and multiplication ranges. No shorter accessible
   sheaf theorem was found. The matching `multiplication_range` in
   IdealTimesQuasiCoherentAffineSections is private; its public theorem handles
   first-power products and power-inclusion ranges, not products by arbitrary powers.
   The local helper therefore retains a real proof from the existing public lemmas.
4. PASS: checked the affine-cover reduction, transport of both annihilator hypotheses,
   the quotient-map square, the lifted section, the scalar-composite identity and
   preservation of ideal multiples. This follows the commutative algebra argument in
   [Stacks Tag 0888](https://stacks.math.columbia.edu/tag/0888), read online because the
   literature checkout is absent here. All proof imports supply declarations used
   in the proof and are plain imports; the public import supplies the signature.
   All four old proof dependencies remain used, so `No longer needed: None` is
   complete. Read `dag/units/sk-thm-p1.json`, including `realized`: no realized step
   is bypassed, and the original scalar quasi-inverse route is retained.
5. PASS: only `proof`, `proof_deps`, and `proof_origin` differ in the existing node.
   Every dependency has its stated Lean declaration; the union of step `uses` equals
   `proof_deps`. The seven dependencies match coherence, kernels, cokernels/images,
   ideal powers, tensor sections, affine vanishing and scalar quasi-inverses in Lean.
   The two private helpers are fully proved implementations of these existing facts.

Changes in this reading: added source-and-proof docstrings to the two private helpers
and this review record. The proof needed no mathematical repair. The automated width
check confirms all Lean lines are at most 100 characters. Closed holes remain one
(`AlgebraicGeometry.coherentMap_reduction_torsion_kernel`); added holes remain zero.
