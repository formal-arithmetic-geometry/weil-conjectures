## Worker report

This delivery states `AdicCompletion.exists_prime_quotient_completion_component_dimension_pred`
in `Sheaf.RingTheory.CatenaryCompletionHyperplane`. Its sole proof is `sorry`.
There are no definitions or auxiliary postponed theorems. The node statement is unchanged.
The added statement dependency `def-exc-excellent-ring` is already landed and supplies
`IsCatenaryRing`; the node already spelled out this notion inline, so this addition only
records the existing interface used by the theorem.

Source read: `literature/stacks-project/more-algebra.tex`, lines 32325–32400,
Tag 0AW3, especially the paragraph beginning “Assume d > 1”; also
`literature/stacks-project/algebra.tex`, lines 25463–25469, Tag 00NI.
The item states the prime-quotient refinement of that hyperplane argument, with catenarity
explicit. Its six proof steps, including component separation and flat going down, are
included in the declaration docstring with every proof-dependency id.

Every hypothesis and clause is rendered as follows:

- A commutative ring is `(A : Type u) [CommRing A]`, with `u` explicitly declared.
- Noetherian is `[IsNoetherianRing A]`; local is `[IsLocalRing A]`;
  a nonzero domain is `[IsDomain A]`.
- Catenary is `(hcat : IsCatenaryRing A)`, the existing bounded-chain and equal-saturated-
  length definition, including zero-length intervals.
- The unique maximal ideal is `IsLocalRing.maximalIdeal A`. The completion `B` is the actual
  canonical `AdicCompletion (IsLocalRing.maximalIdeal A) A`, not an arbitrary algebra.
- `q` is an ideal of this completion, and `hq : q ∈ minimalPrimes ...` is exactly its
  minimal-prime condition. `hdim` identifies the dimension of `B / q` with the natural `d`.
- `hleast` compares this `d` with the dimension of every minimal-prime quotient of the same
  completion. No equidimensionality is assumed.
- `hd : 1 < d` and `hlt : (d : WithBot ℕ∞) < ringKrullDim A` give both strict inequalities.
  Using a natural `d` loses no case: a minimal-prime quotient of a Noetherian local ring
  is a nonzero Noetherian local ring of finite dimension.
- The existential `f : A` has `f ≠ 0` and `f ∈ IsLocalRing.maximalIdeal A`.
- `p ∈ (Ideal.span {f}).minimalPrimes` says exactly that `p` is prime minimal over `fA`.
  Membership includes primality and ideal containment, rather than merely a radical condition.
- `r` belongs to `minimalPrimes` of the canonical completion of `A / p` at
  `(IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk p)`.
  Because `p` is prime in a local ring, it is proper and contained in the maximal ideal;
  its quotient is local with unique maximal ideal equal to precisely this image ideal.
  Thus this is the maximal-ideal completion in the node, with no arbitrary local-ring
  instance or map supplied by the caller.
- `ringKrullDim (A ⧸ p) + 1 = ringKrullDim A` renders `dim(A/p) = dim A - 1`.
  Both rings are nonzero Noetherian local rings of finite dimension, and the source
  hypotheses force `dim A > 1`, so these are equivalent finite-integer identities.
  The additive form avoids truncated subtraction in `WithBot ℕ∞`.
- The next equality gives the dimension of the completion modulo `r` as
  `((d - 1 : ℕ) : WithBot ℕ∞)`, exactly the stated component dimension.
- The final conjuncts `0 < d - 1` and the cast strict inequality with `ringKrullDim (A ⧸ p)`
  explicitly include the node's “in particular” clause.

Statement dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, its docstring and
  `isNoetherianRing_iff_ideal_fg` identify the finitely generated ideal condition.
- `Mathlib.RingTheory.AdicCompletion.Basic` (publicly through `.Algebra`): `AdicCompletion`,
  the compatible inverse-limit family, with the real commutative ring structure from `.Algebra`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim : WithBot ℕ∞`, the supremum
  of strict prime-chain lengths.
- `Sheaf.RingTheory.ExcellentRing`: `IsCatenaryRing`, `IsPrimeChain`,
  `IsSaturatedPrimeChain`; this matches the inline node definition and Stacks 00NI exactly.
- Additional standard Mathlib notions used directly are `IsLocalRing.maximalIdeal`,
  `minimalPrimes`, `Ideal.minimalPrimes`, `Ideal.span`, `Ideal.Quotient.mk`, and `Ideal.map`.

All recorded proof-dependency modules are imported without `public`: finite minimal primes
(`Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`), going down (`.Ideal.GoingDown`),
completion Noetherianity (`WeilConjectures.RingTheory.AdicCompletionNoetherian`, read with
`scompile.py --source`), dimension drop (`Mathlib.RingTheory.KrullDimension.Regular`),
completion localness (`.AdicCompletion.LocalRing`), completion faithful flatness
(`.Flat.FaithfullyFlat.Algebra` together with the completion imports), completion quotient
(`Sheaf.RingTheory.LocalCompletionQuotient`), height bounds and local finite dimension
(`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`), prime avoidance (`.Ideal.Operations`),
and existence of minimal primes below primes (`.Ideal.MinimalPrime.Basic`, already public).
No dependency module is repaired, and no proof import closes a cycle.

Edge cases checked: a field, DVR, and any ring of dimension at most two admit no integer
`1 < d < dim A`; the zero ring is excluded by the domain/local hypotheses; `d = 1` is
correctly excluded, while `d = 2` permits component dimension one. A nonreduced completion
is permitted: neither reducedness nor domainhood of the completion is assumed. An empty
list of positive-dimensional component intersections is permitted in the proof, where
avoiding `(0)` still enforces `f ≠ 0`. Singleton comparable-prime intervals are covered by
`IsCatenaryRing`. No bound on the universe `u` is imposed. The result does not require
that the produced component be a least-dimensional component of the new completion.

Searches made with the required wrapper (raw records retained in sandbox `searches.jsonl`):

- LeanFinder: “Hyperplane reduction of a non-equidimensional completion of a catenary
  Noetherian local domain”: eight hits, only standard dimension inequalities, principal
  quotient dimension drop, and DVR results. None states the theorem.
- Loogle: `"catenary"`: zero hits.
- Mathlib grep: `catenary|equidimensional` in `RingTheory`: zero hits.
- LeanSearch: “A catenary Noetherian local domain with a completion component of dimension d
  has a prime hyperplane quotient with completed component dimension d minus one”: eight
  hits including quotient dimension drop, finite dimension, and height estimates; no match.
- `rg` over upstream `WeilConjectures` for `catenary|Catenary` and the exact item id found
  no upstream statement or definition of catenarity. Broader dimension/completion searches
  found only general algebra infrastructure.
- `rg` over `lean/Sheaf` for `catenary|Catenary` found the existing `ExcellentRing` interface
  and Ratliff consumers. The exact item id occurs only as a proof citation in Ratliff's
  docstring; there is no existing declaration of this hyperplane refinement.
- Searched the upstream-name index `dag/lean_names_upstream.json` together with Mathlib,
  upstream, and side sources for the item id and proposed theorem name: no duplicate.

No statement dispute, correction, missing notion, or unusable statement dependency was found.

Validation: prescribed `scompile.py Q88 lem-per-catenary-completion-hyperplane` compiled
both the sandbox module and the library module cleanly, 2.3 seconds each, exit 0.
The interrupted first compiler session had no retained output and no remaining process;
the successful invocation was rerun with its output retained in sandbox `compile.log`.

## Second reading by Q88

Author's clause-by-clause self-check, not an independent-agent review; the dispatcher brief
forbids starting other agents, and the maintainer supplies independent review after delivery.
I reopened the item JSON, source paragraph, `IsCatenaryRing` definition, minimal-prime
membership definition, and final Lean signature. All input hypotheses are present,
including least dimension and catenarity. All witnesses and four output clauses are present.
I specifically checked that `p` is minimal over `fA`, not just a prime containing `f`,
that the second completion is of `A/p` rather than of `A/fA`, and that the final `r`
is minimal in that completion, not an arbitrary prime. The completion ideal is the
maximal ideal's image, which is the quotient's unique maximal ideal for each witnessed
prime `p`. The additive dimension identity is equivalent on these finite local domains.
No stronger catenarity, regularity, reducedness, or universal-catenarity assumption was
introduced. All variables and universes are explicit. No hidden `let`, private notation,
local instance, hollow definition, or proof other than `sorry` occurs. No mismatch was
found and no statement correction was made.
