## Worker report

The module `Sheaf.TraceFormula.CompleteToricMonomialFactors` states
`complete_toric_monomial_factors`.  It uses the canonical completed toric
models and charts from `Sheaf.TraceFormula.CompleteToricKatoRecognition`.
The proof is `sorry`, as required for a stage-2 statement.

The first conjunct renders the field case.  Its binders are a field `k`, an
exponent `q : P`, and factors `b c` in `CompletedLocalModel k P n`.  The
hypothesis `b * c = completeToricChart k P n q` is the displayed monomial
factorization, and the conclusion supplies `r : P` and a unit `u` with
`b = u * completeToricChart k P n r`.

The second conjunct renders the Cohen case.  It quantifies a commutative local
ring `C`, residue characteristic prime `p`, a proof `IsCohenRing p C`, and a
parameter `θ` satisfying
`θ - p ∈ completedLocalModelBoundaryIdeal C P n`.  It then quantifies `q`,
`b`, and `c` in the quotient `cohenCompleteToricRing C P n θ`, assumes their
product is `cohenCompleteToricChart C P n θ q`, and supplies `r` and a unit
`u` with the corresponding factorization.  The binders `P`, its
`IsFineSaturatedMonoid (Multiplicative P)` instance, sharpness, and `n : ℕ`
are shared by both cases, so `q = 0`, the trivial monoid, and `n = 0` remain
included.

Dependency declarations used:

- `Sheaf.TraceFormula.CompleteToricKatoRecognition.completeToricChart`.
- `Sheaf.TraceFormula.CompleteToricKatoRecognition.cohenCompleteToricRing`.
- `Sheaf.TraceFormula.CompleteToricKatoRecognition.cohenCompleteToricChart`.
- `AddMonoidAlgebra.CompletedLocalModel` and
  `AddMonoidAlgebra.completedLocalModelBoundaryIdeal` from
  `Sheaf.RingTheory.LogRegularSaturationNormality`.
- `IsCohenRing` from `WeilConjectures.RingTheory.CohenRing`.
- `IsFineSaturatedMonoid` from `Sheaf.AlgebraicGeometry.LogRegularPair`.

The proof dependency is the statement
`Sheaf.TraceFormula.CompleteToricKatoRecognition.complete_toric_kato_recognition`,
which supplies the complete-local recognition equality used by the recorded
localization-inverse argument.

Edge cases checked from the source proof are `q = 0` (then `bc = 1`),
`P = {0}` (the localization inverts only `1`), and `n = 0` (no parameter
variables).  No perfection assumption on the Cohen residue field was added.

Searches made:

- `msearch.py ... leanfinder "A factor of a complete saturated toric monomial is a unit times a monomial"`: returned polynomial/UFD factorization results such as `MvPolynomial.dvd_monomial_one_iff_exists`, but no complete toric model match.
- `msearch.py ... loogle "completeToricChart, CompletedLocalModel, IsUnit"`: no hits (these are project declarations, not Mathlib declarations).
- `msearch.py ... grep "complete_toric_monomial_factors|monomial_factors" Sheaf`: no hits.
- `rg` over `WeilConjectures/` and project `lean/Sheaf`: found only the canonical completed-model and Kato-recognition declarations, with no duplicate factor theorem.

The source node statement is retained verbatim and no statement correction or
new node was needed.

## Second reading by Q120

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
