## What changed

Proved `Algebra.exists_algebraMap_eq_of_isAlgebraic_of_finite_purelyTranscendental`
in `Sheaf.FieldTheory.FinitePurelyTranscendentalConstants`, preserving its signature and
public imports. Added one proved private helper establishing normality of the finite
multivariate polynomial ring by induction, using the existing one-variable normality
instance and the empty/successor polynomial equivalences.

The main proof transports integrality to the rational function field, descends to the
normal polynomial ring, reflects integrality along its injective fraction-field map,
and applies `IsIntegral.isUnit` and `MvPolynomial.dvd_C_iff_exists` to the nonzero case.
The zero case is handled separately. The argument covers zero variables, arbitrary
characteristic and imperfect base fields. The only added proof import is
`Mathlib.RingTheory.Algebraic.Integral`. The node's proof and proof dependencies now
record this implementation. The unit route is unchanged.

Validation: the delivered Lean module compiled cleanly through `lcompile.py` in 2.2 seconds.
No warnings or errors remain; all Lean lines are at most 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`Algebra.exists_algebraMap_eq_of_isAlgebraic_of_finite_purelyTranscendental`
(node `lem-trf-pure-transcendental-relatively-algebraically-closed`).
The private helper `Algebra.finite_mvPolynomial_isIntegrallyClosed` is also proved.
No holes remain and no holes were added or split off.

## No longer needed

No existing imports were removed. No Sheaf module is withdrawn.
The proof dependency `def-kun-transcendence-degree` is unnecessary: the specified
fraction-field equivalence already supplies the entire polynomial presentation;
no transcendence-degree calculation or algebraic-independence theorem is used.
It remains a statement dependency, and the corresponding public import is preserved.
All other original proof dependencies remain used. The explicit extraction of a
nonzero constant term is replaced by Mathlib's integral-unit theorem and the divisor
lemma applied to the constant 1. This does not add any unfinished dependencies.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original DAG's polynomial normalization and
constant-term subargument can be implemented more concisely with the existing
Mathlib integral-element API. Stacks 057K uses this constant-field input implicitly;
the proof remains an agent-written expansion, as its existing proof_origin records.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
