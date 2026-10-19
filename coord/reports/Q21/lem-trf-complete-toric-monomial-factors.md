## Worker report

The module `Sheaf.TraceFormula.CompleteToricMonomialFactors` states
`complete_toric_monomial_factor`. It imports the canonical completed toric models and
charts from `Sheaf.TraceFormula.CompleteToricKatoRecognition`.

The hypotheses render as follows. `P : Type u` with `[AddCommMonoid P]` is the additive
commutative monoid in the node; `hP : IsFineSaturatedMonoid (Multiplicative P)` gives
finite generation, integrality, and saturation; `hsharp : ∀ q, IsAddUnit q → q = 0`
is sharpness; and `n : ℕ` is the nonnegative parameter count. The first conjunct
quantifies a field `k`, a monoid element `q`, and `b,c` in the canonical
`CompletedLocalModel k P n`; its equation uses the canonical chart monomial and its
conclusion gives `r : P` and a unit `u` with `b = u * z^r`. The second conjunct
quantifies a local coefficient ring `C`, residue-characteristic prime `p`, the
canonical `IsCohenRing p C` predicate, and `θ` satisfying
`θ - p ∈ completedLocalModelBoundaryIdeal`; it then states the same factorization in
the canonical quotient `cohenCompleteToricRing C P n θ`, using
`cohenCompleteToricChart`. Both conjuncts quantify every `q`, `b`, and `c`, exactly
covering the field and Cohen quotient alternatives in the node.

Dependency declarations used:

* `Sheaf.TraceFormula.CompleteToricKatoRecognition`, `completeToricChart`,
  `cohenCompleteToricRing`, and `cohenCompleteToricChart`.
* `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`,
  `AlgebraicGeometry.IsFineSaturatedMonoid` (through the imported recognition module).
* Mathlib `AdicCompletion`/`IsAdicComplete` through `CompletedLocalModel`.
* `Sheaf.RingTheory.CohenRing`'s `IsCohenRing` predicate through the imported
  recognition module.

Edge cases checked against the node proof: `q = 0` gives the factorization of `1`; the
trivial monoid `P = {0}` leaves only units; and `n = 0` is represented by `Fin 0` in
the canonical model with no parameter variables. The statement imposes no perfection
condition on the Cohen residue field.

Searches for an existing declaration found no match. LeanFinder and LeanSearch queries
for factors of monomials in complete saturated toric local rings returned only ordinary
power-series, polynomial, and localization lemmas. Loogle queries involving
`Associated`, `AddMonoidAlgebra`, `IsLocalization`, and `IsUnit` returned no declaration
of this complete toric statement. Grep over Mathlib and both project source trees for
`toric.*monomial`, `monomial.*unit`, and complete-model recognition found only the
canonical model/chart declarations used above. The existing DAG dependency
`lem-trf-complete-toric-kato-recognition` supplies the exact recognition interface, so no
new definition or dependency repair was needed.

The theorem proof is `sorry`, as required for stage 2.

## Second reading by Q21

I reread the node and the file clause by clause. The Lean hypotheses preserve the same fs,
sharp, and nonnegative-`n` conditions. Its first conjunct is precisely the field model
case, with the canonical `CompletedLocalModel`, chart monomials indexed by `P`, and a
unit-times-monomial conclusion. Its second conjunct is precisely the Cohen quotient case,
including prime `p`, the Cohen-ring predicate, the boundary condition on `θ`, and the
same factorization conclusion in the quotient. The empty parameter set (`n = 0`), zero
monoid, and `q = 0` cases are admitted. No hypothesis or conclusion was added or dropped.
The file compiles cleanly with the prescribed `scompile.py` wrapper.
