## What changed

Replaced the proof of `Padic.local_field_coefficient_stages` in
`Sheaf.NumberTheory.Padics.LocalFieldCoefficientStages` with a proof from
`Padic.exists_integral_basis`, `Padic.extension_integers_dvr`, and Mathlib.
The restricted field inclusion is constructed explicitly. The integral basis supplies
finite freeness; DVR factorization supplies a positive ramification exponent.
The quotient tensor equivalence supplies finite freeness after reduction. Finite
residue fields give finite quotients, and properness gives local quotients. Membership
of the coefficient prime in the maximal ideal gives the common annihilating power.
Transition maps and invariance under changing either uniformizer by a unit are proved
on representatives, including the heterogeneous equalities of quotient maps.

Added seven proved private helpers for these algebraic arguments. Replaced the private
import `Mathlib.Topology.Algebra.Valued.LocallyCompact` by private imports of
`Mathlib.RingTheory.TensorProduct.Quotient`, `Mathlib.RingTheory.TensorProduct.Free`,
and `Mathlib.RingTheory.Ideal.Quotient.Index`. Existing public imports and the theorem
statement are unchanged. Updated the item's proof plan and dependency list to match.
No definitions, public interfaces, consumer modules, or unit routes were changed.

Validation: the complete module compiled through `lcompile.py` in 22.3 seconds,
with no errors or warnings. A source comparison confirmed that the theorem signature
is unchanged, and the source contains no `sorry` tokens.

## Proved and sorry left

Closed the sole original hole, `Padic.local_field_coefficient_stages`
(node `lem-pur-local-field-coefficient-stages`). Added zero holes and split off zero
statements. All seven private helpers are proved. The delivery contains no `sorry`.

## No longer needed

Removed `Mathlib.Topology.Algebra.Valued.LocallyCompact`: the underlying rings are
already supplied as DVRs with finite residue fields. The general algebraic theorem
`Ideal.finite_quotient_pow` applies directly, without constructing a separate valued
field structure. Consequently the proof no longer depends on
`lem-weil-valued-dvr-finite-quotients`; its dependency entry is removed. Its other
users and its node are retained.

The extra factorization of the coefficient prime in the old step 6 is unnecessary:
its maximal-ideal membership suffices. The unit-times-uniformizer-power lemma remains
needed for the ramification exponent in step 3. The integral-basis and DVR inputs
remain needed. No Lean module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The old plan's quotient-coordinate
argument can be implemented more directly by Mathlib's quotient tensor equivalence
and base change of finite free modules. The positive valuation of the coefficient
prime already proves its membership in the uniformizer ideal; the further DVR
factorization in the old step 6 was redundant. The updated proof preserves the
blueprint's arithmetic input and the purity-transport unit route.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
