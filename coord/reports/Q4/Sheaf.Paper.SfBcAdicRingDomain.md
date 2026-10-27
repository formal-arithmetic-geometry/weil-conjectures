## What changed

Proved both theorems in `Sheaf.Paper.SfBcAdicRingDomain`, with every existing
signature and definition unchanged. The arithmetic theorem assembles the DVR
properties, proves residue characteristic l and l^n-annihilation from the spectral
norm of l, constructs the adic datum, and retains the exact two-term complex,
differential and augmentation from `standard_quotients_perfect`. Perfectness is
transported through that augmentation to the standard derived-category instance.
The completed-domain theorem proves all four equalities by reflexivity, including
the three-clause full subcategory and the positive-exponent transition maps.
Updated the existing node's proof route to name the coefficient finiteness API.

Validation: both complete proofs compiled through lcompile.py (6.0 seconds).
Searches: LeanFinder found residue-field and characteristic interfaces, Loogle
found `CharP.charP_iff_prime_eq_zero`, and Mathlib/source grep found the spectral
nonarchimedean theorem, norm_p_lt_one and Ideal.pow_mem_pow. No replacement
for the whole package theorem was found or needed.

## Proved and sorry left

Closed 2 of 2 holes:
- `AlgebraicGeometry.Scheme.sf_bc_adic_ring_domain`.
- `AlgebraicGeometry.Scheme.sf_bc_adic_completed_domain`.

Added 0 holes; split off 0 statements. No sorry remains in the delivery.

## No longer needed

Removed proof import `Mathlib.Topology.Algebra.Valued.LocallyCompact`: quotient
finiteness comes directly from the already proved
`Padic.finite_coefficientExtensionRing`. Added the explicit proof import
`Mathlib.GroupTheory.OrderOfElement` for finite additive order of the first
quotient. No project module or existing declaration is withdrawn. The node
`lem-weil-valued-dvr-finite-quotients` remains relevant for its canonical
quotient-transition surjectivity clause, realized by
`Ideal.Quotient.factor_surjective`; its valuation-specific finiteness proof
is not repeated. All other declared proof dependencies are used, and the unit
route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was necessary. The existing finite coefficient
interface makes it unnecessary to re-establish quotient finiteness using a
fresh valued-field structure. The generic arithmetic theorem constructs its
datum directly, since the published `pbcPadicCoefficientDatum` specialization
has coefficient universe u+1 while this theorem allows every universe u.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
