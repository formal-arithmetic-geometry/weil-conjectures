## Worker report

The module defines `Algebra.IsRelativeGlobalCompleteIntersection` in
`Sheaf.Paper.RelativeGlobalCompleteIntersection`.

The binders `{R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)` render the
commutative base ring, target ring, and ring map. The definition introduces
natural numbers `n` and `c`, a family `relations : Fin c → MvPolynomial (Fin n) R`,
and an `R`-algebra equivalence from the quotient by
`Ideal.span (Set.range relations)` to `S`. This is the presentation
`S ≅ R[x₁,…,xₙ]/(f₁,…,f꜀)`.

For each ideal `p : Ideal R` and explicit hypothesis `_hp : p.IsPrime`, the
local instance renders a prime of `R`; `p.Fiber` is the fibre ring
`κ(p) ⊗[R] T`. The implication hypothesis
`Nontrivial (p.Fiber T)` renders that the fibre is nonzero. Its conclusion
`topologicalKrullDim (PrimeSpectrum (p.Fiber T)) = (n - c : ℕ)` renders that
the spectrum has dimension `n-c` (with natural subtraction, hence truncation
when `c > n`).

Dependencies used: `MvPolynomial` from `Mathlib.Algebra.MvPolynomial.Basic`,
`Ideal.Fiber` from `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`,
`topologicalKrullDim` from `Mathlib.Topology.KrullDimension`, and ideal
quotients from `Mathlib.RingTheory.Ideal.Quotient.Operations`.

Edge cases checked: `n = 0` and `c = 0` are represented by `Fin 0`; empty
relation families give the zero-span ideal; `c > n` uses truncated natural
subtraction as required by the node's remark; zero fibre rings are excluded by
`Nontrivial`; prime hypotheses are explicit because `Ideal.Fiber` requires the
`p.IsPrime` instance.

Searches made: the node's recorded LeanSearch, LeanFinder, Loogle, grep, and
local-search queries found only standard-smooth predicates and presentation
building blocks, with no complete-intersection predicate. Additional `rg`
searches in Mathlib and `WeilConjectures` found no matching declaration.

## Second reading by J1

Read Stacks Algebra Definition 00SP in `algebra.tex` and the node together with
the Lean file. The source fixes a commutative ring map `R → S`, a finite
presentation with `n` variables and `c` equations, and dimension `n-c` for
each nonempty fibre. It assumes no Noetherian, flatness, or characteristic
condition.

- Objects: `{R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)` is the ring
  map; `letI : Algebra R S := f.toAlgebra` uses precisely its algebra structure.
  `∃ (n c : ℕ) (relations : Fin c → MvPolynomial (Fin n) R)` is the finite
  family of equations in `R[x₁,...,xₙ]`. Verdict: matches.
- Presentation: `∃ _e : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range
  relations)) ≃ₐ[R] S` states an `R`-algebra isomorphism with the indicated
  quotient. The equivalence is with the algebra structure induced by `f`.
  Verdict: matches the source's presentation of the ring map.
- Prime and nonempty fibre: `∀ (p : Ideal R) (_hp : p.IsPrime)` ranges over
  all primes; `Nontrivial (p.Fiber ...) →` tests the quotient presentation's
  residue-field fibre. `Ideal.Fiber` reverses the tensor factors compared
  with the node, by the canonical tensor symmetry. Verdict: matches.
- Dimension: `topologicalKrullDim (PrimeSpectrum (p.Fiber ...)) =
  (n - c : ℕ)` computes the topological dimension of that fibre spectrum.
  Together with `c ≤ n` under the nonempty-fibre hypothesis, this says its
  dimension is the integer `n-c`. Verdict: matches after correction.

The first reading omitted `c ≤ n`. Natural subtraction had silently made
`n-c = 0` when `c > n`, admitting nonempty zero-dimensional fibres, contrary
to the node's explicit `T = 0` edge case. I added `c ≤ n` to the consequence
of each nonempty-fibre hypothesis. The universal condition then forces every
fibre empty if `c > n`; for a finite-presentation algebra this means `T = 0`.
The node text and the `lean.statement` signature were not changed.

Edge cases: `Fin 0` handles zero variables and zero equations; the empty
equation family generates the zero ideal. The zero target and an empty base
spectrum make the fibre condition vacuous, as in the source. A nonzero fibre
with `c > n` is now rejected. No characteristic, finiteness, or Noetherian
instance was introduced, and `Type*` permits independent universes for
`R` and `S`.

Independent searches: LeanFinder query `finite presentation of algebra with
pure dimensional fibers` and query `relative complete intersection
commutative ring map expected dimension each nonempty fiber` returned only
standard-smooth predicates; Loogle queries `"IsCompleteIntersection"` and
`"global complete intersection"` returned no match. `rg` over Mathlib's
RingTheory, the upstream `WeilConjectures`, and this project's `lean/Sheaf`
found `Algebra.IsGlobalCompleteIntersection` in
`Sheaf.RingTheory.CompleteIntersectionOverField`; its signature requires a
field and therefore covers only a special case. No existing declaration
states this node over an arbitrary commutative ring.

