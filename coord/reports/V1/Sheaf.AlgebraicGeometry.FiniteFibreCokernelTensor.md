## What changed

Proved `AlgebraicGeometry.subsingleton_fibreTensor_sectionCokernel` in
`lean/Sheaf/AlgebraicGeometry/FiniteFibreCokernelTensor.lean`, preserving its signature
and docstring. Added the proof-only import
`Mathlib.LinearAlgebra.TensorProduct.RightExactness` for tensor-map surjectivity.
Updated the existing node's proof and proof_origin to describe the actual argument.

The affine-chart square is a pullback. Its induced fibre square transports the
closed-immersion hypothesis, and `Spec.fiberToSpecResidueFieldIso` identifies that
fibre map with the spectrum of the scalar tensor map. The affine closed-immersion
criterion and the ΓSpec isomorphisms give scalar-map surjectivity. Tensoring the
quotient map is surjective and zero, since every source tensor is `k ⊗ 1` and the
quotient kills `1`. This proves the tensor quotient is subsingleton.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.subsingleton_fibreTensor_sectionCokernel`
(node `lem-weil-pbc-finite-fibre-cokernel-tensor`). No holes remain or were added.
The proof uses only Mathlib, with no Sheaf or WeilConjectures proof dependencies.
Local compilation passed without errors or warnings. The delivery dry run checks
all declaration axioms as well.

## No longer needed

No imports or DAG nodes are pruned. All three existing proof dependency nodes are
still used through their Mathlib realizations, combined in
`Spec.fiberToSpecResidueFieldIso` for the fibre identification and in the affine
closed-immersion criterion. The full `TensorProduct.lTensor_exact` argument is
unnecessary: `LinearMap.lTensor_surjective` plus explicit vanishing suffices.
No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical errors found. The module initially had no proof-dependency imports;
its three DAG dependencies are Mathlib results already accessible through its
public imports. No additional statement modules were needed. Empty fibres are
covered because none of the argument assumes the tensor algebra is nontrivial.

## Second reading by V1

1. **Unchanged visible declarations.** Diffed the delivered module against the
repository version. The theorem signature and all existing declarations are unchanged;
the only source changes are a proof-only import and the theorem proof. Verdict: pass.
2. **Proof validity and axioms.** Compiled the module with `lcompile.py`; it passes
without errors or warnings and contains no `sorry`, `axiom`, `unsafe`, `opaque`,
`extern`, or `implemented_by`. The proof uses the closed-immersion fibre
identification, scalar-map surjectivity, and tensor quotient surjectivity, ending in
the required `Subsingleton`. Verdict: pass.
An independent scratch copy with `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`.
3. **Statements and split-offs.** No statements were split off and no new holes were
added. The sole theorem is exactly the existing node statement, and the argument
handles the zero/empty-fibre case. Searches found no duplicate declaration in the
library or Mathlib. Verdict: pass.
4. **Shortest route and pruning.** The proof uses Mathlib's affine fibre
identification and `LinearMap.lTensor_surjective`; it does not introduce an
unnecessary exactness argument. Imports are minimal: the added right-exactness import
is proof-only. No old proof dependency or unit route is bypassed. Verdict: pass.
5. **DAG agreement.** The node's proof and proof origin describe the implemented
affine pullback, closed-immersion, scalar-surjectivity, and tensor-quotient steps;
`proof_deps` and the realized unit route remain consistent. Verdict: pass.

Second-reading changes: added this review record only. No proof repair was necessary.
