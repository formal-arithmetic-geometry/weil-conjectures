## Worker report

The module `Sheaf.RingTheory.CatenaryCompletionHyperplane` states
`IsCatenaryRing.exists_hyperplane_prime_quotient`, with its sole proof `sorry`.
It introduces no new definitions and leaves the node unchanged except for `lean`.
Source read: Stacks Project, `more-algebra.tex`, Tag 0AW3,
`lemma-not-formally-catenary`, especially lines 32374–32385. The node gives the
catenary prime-quotient refinement of that hyperplane argument; its six proof
steps are reproduced in the declaration docstring, with their dependency ids.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative Noetherian local domain A is `(A : Type u) [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]`. `IsDomain` includes
  nontriviality. Its unique maximal ideal is `IsLocalRing.maximalIdeal A`.
- Catenarity is the recorded `IsCatenaryRing A`, bound as `hcat`; this includes
  both finite chain bounds in prime intervals and equal saturated-chain lengths.
- B is exactly `AdicCompletion (IsLocalRing.maximalIdeal A) A`, not an arbitrary
  ring with a completion-like property.
- The given minimal prime q is `q : Ideal B` with `hq : q ∈ minimalPrimes B`.
  This membership already includes primality and minimality.
- The integer d is bound as `d : ℕ`, with `hdim : ringKrullDim (B ⧸ q) = d`.
  No dimension is replaced by a truncating conversion to natural numbers.
- Least dimension among all minimal-prime quotients is `hleast`, quantifying over
  every `q' ∈ minimalPrimes B` and requiring `↑d ≤ ringKrullDim (B ⧸ q')`.
- The strict bounds are `hd : 1 < d` and
  `hdA : (d : WithBot ℕ∞) < ringKrullDim A`.
- The conclusion supplies `∃ f : A, f ≠ 0 ∧ f ∈ IsLocalRing.maximalIdeal A`.
- The prime p minimal over fA is
  `∃ p ∈ (Ideal.span ({f} : Set A)).minimalPrimes`. `span {f}` is fA;
  minimal-prime membership includes primality, containment and minimality.
- The completion of A/p is
  `AdicCompletion ((IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk p)) (A ⧸ p)`.
  Since p is prime in local A, p is proper and contained in m, A/p is a nonzero
  local domain, and the image of m is exactly its unique maximal ideal. Thus
  this is its maximal-ideal completion, with no arbitrary choice of ideal.
  This encoding also avoids an unnecessary dependent typeclass witness for p.
- The existential r is an ideal of that actual completion; its membership in
  `minimalPrimes` asserts precisely that it is a minimal prime.
- `ringKrullDim (A ⧸ p) + 1 = ringKrullDim A` renders
  dim(A/p) = dim A - 1 equivalently. Both dimensions are finite nonnegative
  integers because the rings are nonzero Noetherian local rings, and dim A > d > 1.
  Writing the successor equation avoids subtraction at the bottom/infinite values
  of `WithBot ℕ∞`; it adds or removes no condition in this setting.
- The second dimension equation is the literal dimension of the quotient of that
  completion by r, equal to `((d - 1 : ℕ) : WithBot ℕ∞)`.
- The final two conjuncts explicitly retain `0 < d - 1` and
  `((d - 1 : ℕ) : WithBot ℕ∞) < ringKrullDim (A ⧸ p)`.

Statement dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (also available through
  the excellent-ring import); all ideals are finitely generated.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`; its actual ring
  structure comes from the publicly imported `Mathlib.RingTheory.AdicCompletion.Algebra`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim : WithBot ℕ∞`.
- `Sheaf.RingTheory.ExcellentRing`: `IsCatenaryRing`, listed in the declaration
  record of `def-exc-excellent-ring`, with its full chain definitions read.
- `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`: `minimalPrimes`,
  `Ideal.minimalPrimes`, `Ideal.IsMinimalPrime`.
- `Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs`: `IsLocalRing.maximalIdeal`.

Proof dependencies are imported privately in accordance with stage 2:
`Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`
(`Ideal.finite_minimalPrimes_of_isNoetherianRing`,
`minimalPrimes.finite_of_isNoetherianRing`),
`Mathlib.RingTheory.Ideal.GoingDown` (`Algebra.HasGoingDown.of_flat`),
`WeilConjectures.RingTheory.AdicCompletionNoetherian`
(`AdicCompletion.isNoetherianRing`),
`Mathlib.RingTheory.KrullDimension.Regular`
(`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`),
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
(`Module.FaithfullyFlat.of_flat_of_isLocalHom`),
`Mathlib.RingTheory.AdicCompletion.LocalRing` (completion local ring and maximal ideal),
`WeilConjectures.RingTheory.LocalCompletionQuotient`
(`AdicCompletion.exists_local_completion_quotient`),
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem` (height bound and finite local dimension),
and `Mathlib.RingTheory.Ideal.Operations` (`Ideal.subset_union_prime`).
`Ideal.exists_minimalPrimes_le` is already in the public minimal-prime import.
No proof-dependency import is omitted.

Edge cases checked: the zero ring is excluded by `IsDomain`; fields and local
rings of dimension at most two cannot meet `1 < d < dim A`. The first permitted
case d = 2 produces completed component dimension 1 and positive quotient
dimension strictly greater than 1. All occurrences of d - 1 are therefore
untruncated subtraction on a positive natural number. Empty sets of other
components or positive-dimensional intersections require no extra hypotheses;
the proof docstring explicitly includes the zero ideal in prime avoidance.
Minimal-prime memberships rule out p = top and r = top. No finiteness assumption
on the residue field, equicharacteristic restriction, universal catenarity,
excellence, or equidimensionality assumption was added. The universe u is explicit,
and every binder is explicit under `set_option autoImplicit false`.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`: “A catenary Noetherian local domain with a minimal
  completion component of least dimension d between one and dim A admits a prime
  quotient minimal over a nonzero hyperplane whose dimension and completed component
  dimension each drop by one”. Eight hits, including
  `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim` and its nonzerodivisor
  version, dimension bounds, and prime-spectrum chain lemmas. None states this
  completed-component prime-quotient conclusion.
- `msearch.py ... loogle '"AdicCompletion", "ringKrullDim"'`: zero hits.
- `msearch.py ... grep 'catenary|hyperplane|equidimensional' RingTheory`: zero hits.
- `rg` of `lean/WeilConjectures/RingTheory` for hyperplane, completion/component,
  and catenary located the existing excellent-ring definitions and unrelated
  completion constructions, with no hyperplane theorem. `grep -rn` of the item id
  in `lean/WeilConjectures` returned no match.
- `rg` of `lean/Sheaf` for completion/hyperplane and the proposed declaration names,
  and of Mathlib, upstream and `dag/lean_names_upstream.json` for
  `exists_hyperplane_prime_quotient|catenary_completion_hyperplane`, found no match.
- The upstream `WeilConjectures.RingTheory.Excellent` was also read: it has an
  alternate existing catenarity interface. This delivery uses the usable interface
  explicitly recorded by the dependency node, without defining either notion anew.

Validation: prescribed `scompile.py` passed both sandbox and library-name compilation,
with no errors or warnings. No statement correction, new node, dependency repair,
or STATEMENT-DISPUTED issue is needed. The independent maintainer review reads
this delivery as specified by the dispatcher brief; no additional agents were started.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
