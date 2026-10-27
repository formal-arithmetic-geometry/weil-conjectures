## What changed

Proved `rationalConeDualIntegralForms` without changing its signature or docstring.
The proof uses the existing rational half-space theorem
`Weil.rationalConeDualFinite`, the only declared proof dependency. A proved private
helper `integral_multiple` clears the finitely many basis denominators using
`IsLocalization.exist_integer_multiples_of_finite` with positive integers, and
extends the integer basis values by `Basis.constr`. Basis extensionality verifies
that this additive homomorphism is the positive multiple of the original form
on every lattice element.

Positive rescaling preserves all defining inequalities. Pointedness makes the
common kernel zero; Mathlib's finite-dimensional double-annihilator theorem
then proves that the scaled forms span the full rational dual. The zero vector
space uses the empty family. For the universal nonempty-family conclusion,
an empty inequality family would make both a nonzero vector and its negative
belong to the cone, contradicting pointedness directly. The reproducing
hypothesis is not needed, but remains unchanged in the theorem signature.

Added only private proof imports: `Mathlib.LinearAlgebra.Dual.Lemmas`,
`Mathlib.RingTheory.TensorProduct.Finite`,
`Mathlib.RingTheory.Localization.FractionRing`, and
`Mathlib.RingTheory.Localization.Integer`.

## Proved and sorry left

Closed 1 hole: `rationalConeDualIntegralForms`
(node `lem-trf-rational-cone-dual-integral-forms`).
Added 0 holes. The item has 0 remaining `sorry`s; the private denominator
helper is fully proved. Nothing was split off.

The proof still depends on the existing, unmodified `sorry` in
`Weil.rationalConeDualFinite`
(node `lem-trf-rational-cone-dual-finite`), as intended by the assigned DAG.
Thus this is a proof from the existing dependency, not a claim that its
transitive axiom closure is already sorry-free.

## No longer needed

None. No original imports, declared dependency nodes, or modules were removed.
The planned rational half-space route and the unit route are preserved.
No new statement or replacement route was needed. No node changes are needed.

## Where the brief, the DAG or earlier work was wrong

No blocking discrepancy. The nonempty-family clause follows from the
half-space description and pointedness alone, so its proof does not need
the supplied spanning and integrality hypotheses. Likewise, the reproducing
hypothesis is unnecessary for the existing conclusion. All hypotheses and
conclusions are preserved verbatim. The rank-zero case, empty generator
family, and empty candidate inequality family are covered by the Lean proof.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
