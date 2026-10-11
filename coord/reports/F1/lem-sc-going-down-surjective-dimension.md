## Worker report

The module `Sheaf.RingTheory.KrullDimension.GoingDown` states
`ringKrullDim_le_of_goingDown_of_surjective`.  It uses Mathlib's
`ringKrullDim` for the Krull dimension of a commutative ring.

The Lean binders render the node as follows.  `R` and `S` are commutative rings and
`φ : R →+* S` is the homomorphism.  `hgoing` says that for prime ideals
`p₁ ≤ p₂` of `R`, and a prime `q₂` of `S` whose contraction is `p₂`, there is a
prime `q₁ ≤ q₂` whose contraction is `p₁`; the two `IsPrime` arguments render the
prime hypotheses and the equality arguments render contractions.  `hsurjective`
is `Function.Surjective (PrimeSpectrum.comap φ)`, exactly the surjectivity of the
spectrum map.  The conclusion is `ringKrullDim R ≤ ringKrullDim S`.

The proof is `sorry` as required for stage 2.  Its docstring records the source
chain argument: choose a prime over the top of a finite chain, apply going down
successively, use distinct contractions for strictness, and take suprema.

Dependency used: the Mathlib declaration `ringKrullDim`, defined in
`Mathlib.RingTheory.KrullDimension.Basic` (line 30), with the chain supremum
construction from `Mathlib.Order.KrullDimension` (line 78).  The spectrum map is
Mathlib's `PrimeSpectrum.comap` from
`Mathlib.RingTheory.Spectrum.Prime.RingHom` (line 34).

Edge cases checked against the statement: the quantification allows the zero
ring and empty prime spectra; no Noetherian, finite type, domain, or nonempty-chain
hypothesis is introduced; both ring universes are independent; equality of
contractions forces strictness even when the displayed going-down inclusion is
non-strict.

Searches made:

* `msearch.py ... leanfinder "going down property ring hom prime ideals surjective spectrum Krull dimension"` returned `ringKrullDim_le_of_surjective`, `Algebra.HasGoingDown`, and related declarations, but no exact theorem.
* `msearch.py ... loogle "ringKrullDim, HasGoingDown, PrimeSpectrum.comap"` returned no hits (`HasGoingDown` unknown).
* `msearch.py ... grep "HasGoingDown|ringKrullDim.*going" RingTheory` found Mathlib's going-down declarations and height lemmas, but no surjective-spectrum Krull-dimension theorem.
* `rg` over Mathlib, `WeilConjectures`, and project `lean/Sheaf` found no declaration with this node's id or theorem name; the only project occurrence is a consumer's docstring reference.

No statement dispute or node correction was needed.

## Earlier second reading (a previous round; superseded)

Reading the node and module together, the theorem has exactly the node's two
hypotheses and its dimension inequality.  `p₁.IsPrime` and `p₂.IsPrime` are
explicit, `q₂.IsPrime` is explicit, and no hypotheses are added.  The contraction
conditions are the equalities `Ideal.comap φ q₂ = p₂` and
`Ideal.comap φ q₁ = p₁`; the order condition is `q₁ ≤ q₂`.  The map in the
surjectivity hypothesis is precisely `PrimeSpectrum.comap φ`.  The conclusion
uses Mathlib's ring Krull dimension, the dependency recorded for the node.  No
mismatch was found.

## Second reading by F1

I independently opened the item node, its only statement dependency
`def-weil-pbc-krull-dimension-ring`, and the delivered module. The repository lacks
`literature/stacks-project/algebra.tex`, so I read the upstream Stacks TeX fetched
from https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex
into the sandbox scratchpad. I read `section-homomorphism-dimension` and
`lemma-dimension-going-up` (Tag 00OH), `definition-going-up-down` (Tag 00HV),
and `definition-Krull` (Tag 00KE). The section introduces no standing extra
hypotheses. Tag 00OH treats going up or going down; this node intentionally
isolates its going-down case, exactly as its title and blueprint use require.

Object/hypothesis/conclusion checklist, matched against the Lean:

- Objects: arbitrary commutative rings R and S are `{R : Type u} {S : Type v}`
  with `[CommRing R] [CommRing S]`; the arbitrary unital ring map is
  `(φ : R →+* S)`. Verdict: exact, independent universes, no domain, field,
  Noetherian, finite-type, or algebra-structure assumptions.
- Going-down inputs: primes p1 and p2 of R, inclusion p1 ⊆ p2, and a prime
  q2 of S over p2 are `∀ ⦃p₁ p₂ : Ideal R⦄, p₁.IsPrime → p₂.IsPrime →
  p₁ ≤ p₂ → ∀ ⦃q₂ : Ideal S⦄, q₂.IsPrime → Ideal.comap φ q₂ = p₂ →`.
  Verdict: exact, with the node's order of quantifiers and hypotheses.
- Going-down output: a prime q1 below q2 contracting to p1 is
  `∃ q₁ : Ideal S, q₁.IsPrime ∧ q₁ ≤ q₂ ∧ Ideal.comap φ q₁ = p₁`.
  Verdict: every clause present, and no stronger inclusion required.
- Spectrum surjectivity is `(hsurjective : Function.Surjective
  (PrimeSpectrum.comap φ))`. I opened `Mathlib.RingTheory.Spectrum.Prime.RingHom`:
  `PrimeSpectrum.comap` takes `q` to `Ideal.comap φ q.asIdeal` with its primality
  proof. Verdict: precisely the node's contraction map, not surjectivity of φ.
- Conclusion is `ringKrullDim R ≤ ringKrullDim S`. I opened the dependency's
  recorded Mathlib declaration in `Mathlib.RingTheory.KrullDimension.Basic`
  and `Order.krullDim` in `Mathlib.Order.KrullDimension`: the former is the
  latter on `PrimeSpectrum R`, and the latter is the supremum of strict finite
  series lengths in `WithBot ℕ∞`. Verdict: exactly the dependency's dimension,
  with the correct direction and with both infinite and empty cases included.

Edge cases: neither ring is required to be nontrivial. Empty spectra have
bottom dimension; for S zero and R nonzero spectrum surjectivity cannot hold,
just as in the node. For R zero the inequality is immediate. Length-zero
chains are single primes, lifted by surjectivity without invoking going down.
Equal p1 and p2 are allowed; q1 = q2 supplies the trivial lift. Unbounded chain
lengths give top dimension. There is no index-set binder or scheme assumption
to restrict; the relevant empty case is the prime spectrum. Characteristic is
unrestricted and both universes are explicitly bound by `universe u v`.

Independent searches (recorded in searches.jsonl):

- LeanFinder: "A homomorphism with surjective map on prime spectra and lifting
  descending prime chains bounds the Krull dimensions" found the quotient
  theorem `ringKrullDim_le_of_surjective`, the order theorem
  `Order.krullDim_le_of_strictComono_and_surj`, and related dimension results.
- Loogle: `ringKrullDim, Function.Surjective` found only the ring-surjective
  quotient inequality and its nonzero-divisor variant, not this statement.
- LeanSearch: "Krull dimension inequality for a ring map satisfying going down
  and surjectivity on prime spectra" was unavailable (Internal Server Error);
  no result is asserted from that service.
- Mathlib grep: `krull.*(down|lift)|going.?down|HasGoingDown` in RingTheory
  found `Algebra.HasGoingDown` and its chain/height lemmas. I opened
  `Mathlib.RingTheory.Ideal.GoingDown`: its predicate is for an already chosen
  R-algebra structure and its chain theorem lifts a single chain with a chosen
  prime over its last member. Neither is this arbitrary-ring-map dimension
  theorem. The explicit hypothesis here unpacks the source definition using
  existing `Ideal.comap`; it introduces no second definition or private notion.
- I searched the source `WeilConjectures` and project `lean/Sheaf` with
  `going.?down|HasGoingDown|lift.*chain|chain.*lift`, and checked the proposed
  theorem name and node id against the upstream-name index. No exact statement
  or name conflict exists. I opened the source's
  `WeilConjectures.Mathlib.Topology.KrullDimension`: its surjective specializing
  map theorem is a theorem about topological spaces, not this ring statement.
  I also opened `Order.krullDim_le_of_strictComono_and_surj`; strict comparison
  reflection for every pair is different from the existential lifting
  hypothesis here, so it is not an existing exact match.

Mismatch and repair: the signature is correct and was retained verbatim in
both the Lean file and `lean.statement`. The proof docstring had compressed
away the node's explicit zero-ring step; I expanded it to all three node steps,
including bottom dimension, the choice over the final prime, descending lifts,
strictness by distinct contractions, and the supremum argument. No new nodes,
dependency modules, or statement correction are needed. There are no hollow
definitions and the sole theorem remains `sorry`, as stage 2 requires. Both
imports are used; the declaration has no namespace prefix or unbound variable.
