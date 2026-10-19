## What changed

Proved `AlgebraicGeometry.noetherianSpace_primeSpectrum_of_finiteType` in
`Sheaf.AlgebraicGeometry.FiniteTypeNoetherianSpectrum`, with its original signature and public
imports unchanged. The proof uses private, fully proved helpers for leading-term cancellation,
compactness of opens, coefficientwise quotient spectra, finite unions, and Noetherian induction.
No definitions, existing statements, consumers or target signatures changed.

The main simplification is to prove the prime-membership consequence of generic principality
by cancelling leading terms directly. This avoids localization denominators and monic division.
For each open U over a domain, this gives U intersect D(C(a)) = D(C(a)f), a compact basic open.
Noetherian induction controls its intersection with the closed complement. Finite-variable
induction and the finite-type polynomial quotient finish the original theorem.

Updated the existing node's proof, proof dependencies and proof origin to match this argument.
Replaced the proof imports of AdjoinRoot and Localization.Away.Basic with
Mathlib.Algebra.Polynomial.CancelLeads. No new module or node is needed: all private helpers
are proved, and their arguments are included explicitly in the existing node's proof steps.
The coefficient-heart unit's route is preserved.

Validation: the final module compiles cleanly through lcompile.py (3.9 seconds after import
pruning). The axiom probe reports exactly propext, Classical.choice and Quot.sound for the main declaration. The algebra lemma permits arbitrary
commutative rings; the domain hypothesis is used only to show V(a) is proper by the zero prime.
The argument explicitly handles zero polynomials, degree-zero polynomials, empty closed sets,
zero ideals, zero variables and zero rings. The finite-type presentation allows independent
universes for R and B, as in the original statement.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.noetherianSpace_primeSpectrum_of_finiteType`
(node `lem-sfb-finite-type-noetherian-spectrum`).

Proved 1 of 1 original sorries. Added 0 holes; split off 0. No sorry remains in the module or
any delivered file. Every private helper has a complete proof.

## No longer needed

Removed proof imports:

- `Mathlib.RingTheory.AdjoinRoot`: monic division is replaced by leading-term cancellation.
- `Mathlib.RingTheory.Localization.Away.Basic`: no localization ring or denominator calculation
  is constructed by this proof.

Removed planned direct node dependencies:

- `lem-weil-pbc-monic-quotient-free`: the least-degree argument is carried out directly with
  Polynomial.cancelLeads, so no monic quotient or power basis is needed.
- `lem-weil-pbc-spec-irreducible-components-minimal-primes`: use the existing Mathlib leaf
  `lem-weil-pbc-spec-irreducible-closed-subsets-primes` directly to identify irreducible closed
  subsets as V(p); minimal irreducible components are unnecessary.
- `def-weil-ring-localization-away`: no explicit localization construction is used. The basic
  open compactness theorem encapsulates its standard localization proof.

Retained `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`. Retained
`lem-weil-pbc-spec-localization-away-basic-open` for the standard compactness justification of
basic opens, paired with the existing Mathlib leaf
`lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`. These are used through Mathlib's
PrimeSpectrum.isCompact_basicOpen. Added the existing Mathlib leaf
`lem-weil-pbc-spec-irreducible-closed-subsets-primes` in place of the minimal-component detour.
No project Lean module was withdrawn. The removed dependencies may still be needed by other
parents; this report prunes them only from this item's direct argument.

## Where the brief, the DAG or earlier work was wrong

The statement is correct and unchanged. Searches through leanfinder, loogle and grep found
only the stronger Noetherian-ring version in Mathlib, so it cannot discharge this statement.
The DAG's localization and monic-division argument is longer than needed: strong induction
with leading-term cancellation gives precisely the prime-membership equivalence used by the
open-set argument, even before reducing to a domain. The original paper is unavailable in
the local collection; the proof remains explicitly agent-origin, as in the original node.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
