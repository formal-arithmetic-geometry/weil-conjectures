## What changed

Proved `AlgebraicGeometry.universally_isHomeomorph_specMap_of_power_generated` in
`lean/Sheaf/RingTheory/PowerGeneratedSpectrumHomeomorphism.lean`, with its signature
and public imports unchanged. Four proved private helpers implement algebra-adjoin
induction, uniqueness of maps into fields, the integral/radicial/surjective criterion,
and nilpotence of the tensor-base-change kernel across arbitrary universes.

The adjoin induction uses the already stated
`Subring.exists_prime_pow_add_mem`. The shorter universal-homeomorphism route uses
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra`:
positive powers in the range give integrality and a spectrum homeomorphism; the
prime-power and prime-multiple conditions give uniqueness of field-valued points;
the proved integral/radicial/surjective criterion then handles arbitrary schemes.
Its tensor-base-change API supplies spectrum surjectivity, from which the kernel
is nil. The generator set after base change is explicitly `{1 tensor x | x in s}`.
The final spectrum homeomorphism follows from Mathlib's all-element power criterion.

Updated the existing DAG node's proof, proof dependencies, and proof origin to
record this route. No definitions, statement signatures, or consumer modules changed.
The node's unit has no realized statement or proof steps that this change bypasses.

Validation: the final module compiles cleanly through `lcompile.py` in 4.4 seconds,
with no warnings. All delivered Lean lines have at most 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.universally_isHomeomorph_specMap_of_power_generated`
(node `lem-pur-power-generated-spectrum-homeomorphism`).

Added 0 holes; split off 0 statements. There are no `sorry` proofs in the delivered
Lean module. All four private helper theorems are proved. The unchanged imported
`Subring.exists_prime_pow_add_mem`
(node `lem-pur-prime-power-addition-subring`) remains an existing dependency with
its own `sorry`; this delivery proves the assigned theorem from that stated lemma.

## No longer needed

Removed redundant direct proof imports `Mathlib.AlgebraicGeometry.Pullbacks`,
`Mathlib.AlgebraicGeometry.PullbackCarrier`, and
`Mathlib.RingTheory.Spectrum.Prime.Topology`; the imported proved universal-homeomorphism
API already supplies them. These modules remain transitive imports, so no module is
claimed to leave the targets' import closure.

The separate final affine-chart gluing argument is unnecessary: the existing
integral/radicial/surjective criterion handles all scheme base changes. None of the
original mathematical proof dependencies is discarded: the fibre-product and
surjective-base-change facts are used through the proved tensor-product API;
the radical criterion is used through
`PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical`; the addition, all-element
power, and tensor-generation/balancing arguments remain. The universal-homeomorphism
definition remains a statement dependency.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The original proof plan missed
the already proved universal-homeomorphism criterion and ring-level tensor-product
API. Their same-universe signatures require lifting the rings to a common universe
for the theorem's larger-universe base changes; the proof transports the concrete
tensor product with `Algebra.TensorProduct.uliftEquiv`. The field-point argument
splits on whether p vanishes in the target field, so it imposes no characteristic
assumption on R or B. The proof also covers zero rings and empty spectra.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
