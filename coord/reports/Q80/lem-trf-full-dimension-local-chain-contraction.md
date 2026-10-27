## Worker report

Item: `lem-trf-full-dimension-local-chain-contraction`, group Q80, stage 2.

The module `Sheaf.RingTheory.FullDimensionLocalChainContraction` states
`Ideal.full_dimension_local_chain_contraction`, with one postponed proof (`sorry`).
It introduces no definitions. The item's node changes only in `lean`.

Hypotheses and objects, matched against the node:

- The commutative nonzero integral domain is `{A : Type u} [CommRing A] [IsDomain A]`.
  `IsDomain` supplies nontriviality and the absence of zero divisors.
- The prescribed maximal ideal is `(m : Ideal A) [m.IsMaximal]`. Its prime instance
  follows from maximality, as required for `Localization.AtPrime m`.
- The ring `B = A_m` is exactly Mathlib's `Localization.AtPrime m`; it is the
  canonical fraction construction, with no arbitrary replacement ring or map.
- The canonical map lambda is `algebraMap A (Localization.AtPrime m)`, sending
  `a` to `a/1`. Contraction is Mathlib's `Ideal.comap` along this very map.
- The nonnegative integer `r` is `(r : ℕ)`; no positive-dimension assumption occurs.
- `dim A = r` is `hA : ringKrullDim A = (r : WithBot ℕ∞)`.
- `dim B = r` is `hB : ringKrullDim (Localization.AtPrime m) = (r : WithBot ℕ∞)`.
  Neither finiteness nor equality of dimensions is silently omitted.

Conclusions, matched clause by clause:

- A chain of length `r` has `r + 1` vertices: the first conjunct existentially
  quantifies `q : Fin (r + 1) → Ideal (Localization.AtPrime m)`.
- Each vertex is prime by `∀ i : Fin (r + 1), (q i).IsPrime`.
- `StrictMono q` means strict inclusion of its ideals whenever the indices increase.
  On this finite linear index set this is exactly the displayed strict prime chain.
- The second conjunct universally quantifies a new `q` with precisely those prime
  and strictness hypotheses; the endpoints are asserted for every such chain,
  not merely for one existentially chosen chain.
- Each contracted ideal is prime by the first universally indexed conclusion,
  `(Ideal.comap (algebraMap A (Localization.AtPrime m)) (q i)).IsPrime`.
- Strictness after contraction is the `StrictMono` conclusion for the function
  `fun i ↦ Ideal.comap (algebraMap A (Localization.AtPrime m)) (q i)`.
- The contracted ideals lie below `m` by the following universally indexed `≤ m`
  clause. The node's final inclusion follows, and all intermediate inclusions
  agree with it by monotonicity.
- The first endpoint is the explicit equality for `q 0` with `⊥`, the zero ideal.
- The final endpoint is the explicit equality for `q (Fin.last r)` with `m`.

Dependencies read and used:

- `def-weil-pbc-localization-at-prime`: recorded `Localization.AtPrime`, from
  `Mathlib.RingTheory.Localization.AtPrime.Basic`. Read its docstring and the
  abbreviation `Localization m.primeCompl`, and the surrounding local-ring and
  domain instances. The residue-field and fibre-ring clauses of that multi-notion
  dependency are not needed by this item.
- `def-weil-pbc-krull-dimension-ring`: recorded `ringKrullDim`, from
  `Mathlib.RingTheory.KrullDimension.Basic`. Read the complete declaration and
  `Order.krullDim` in `Mathlib.Order.KrullDimension`: the supremum of `LTSeries`
  lengths in `WithBot ℕ∞` is exactly the node's notion of dimension.
- Proof dependency `lem-weil-pbc-primes-of-localization`: its Mathlib match is
  `IsLocalization.AtPrime.orderIsoOfPrime` in the first localization module,
  with `IsLocalization.orderIsoOfPrime` in `Mathlib.RingTheory.Localization.Ideal`
  for its away-localization clause. Read both signatures, docstrings and the
  construction by contraction with inverse extension. The latter module is
  explicitly imported as a proof dependency; the former is already public for
  the statement. This item's proof uses only the prime-localization clause.
- `Ideal.comap` in `Mathlib.RingTheory.Ideal.Maps` was read: its carrier is the
  inverse image of the ideal, so this is the stated contraction, not extension.

Source reading: `literature/stacks-project/algebra.tex`, lemma-spec-localization
(Tag 00E3, lines 3163 ff.) gives contraction and inverse extension; definition-Krull
(Tag 00KE, lines 14327 ff.) defines dimension by strict prime-chain lengths.
`literature/stacks-project/morphisms.tex`, lemma-alteration-dimension (Tag 02JX,
lines 13745 ff.), uses the full-dimensional local prime chain in the equality
proof. The theorem docstring records all four node proof steps: finite-supremum
attainment including zero; prime correspondence and strictness; prepend zero;
append the maximal ideal.

Edge cases checked before drafting:

- `r = 0`: `Fin (0 + 1)` is a singleton; both `0` and `Fin.last 0` refer to
  that vertex. `StrictMono` on the singleton is vacuous, while primality and
  both endpoint equalities remain substantive. A zero-dimensional domain is
  a field, so its maximal ideal is zero and the two endpoints are compatible.
- A field with maximal ideal zero realizes that singleton case, including
  positive characteristic. No characteristic restriction occurs.
- `A = ℤ`, `m = (p)` for a prime integer, `r = 1`: the localized prime chain
  is zero strictly below its maximal ideal, contracting to zero and `(p)`.
- The zero ring is correctly excluded by `IsDomain`, as in the node. Empty
  chains are not being used: a chain of length zero has one prime.
- Infinite dimension is correctly excluded by the two equalities to a natural
  number. There is no Noetherian or finite-type assumption, and `u` is arbitrary.

Searches (2026-10-24, prescribed `msearch.py Q80 <item>` wrapper):

- LeanFinder: "If a domain and its maximal localization have dimension r, every
  length r prime chain contracts strictly from zero to that maximal ideal".
  Eight hits included `Ring.krullDimLE_of_isLocalization_maximal`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`, and
  `Ideal.primeHeight_eq_ringKrullDim_iff`. These give bounds or heights and do
  not state existence plus the contraction endpoints of every optimal chain.
- Loogle: `"IsLocalization", "LTSeries"`: zero hits.
- LeanSearch: "A longest prime chain in a maximal localization contracts from
  zero to that maximal ideal": eight hits on the localization maximal ideal,
  lying over and dimension-zero bounds; no exact match.
- Mathlib grep: `LTSeries|chain.*contract|head.*bot|last.*maximal`, subdirectory
  `RingTheory/Localization`: zero hits.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for `full_dimension.*chain|chain.*contraction|chain.*contract|localChainContraction|
  fullDimensionLocalChain|lem-trf-full-dimension-local-chain-contraction` found
  related filtered-colimit contraction modules and the consumer
  `Sheaf.TraceFormula.GenericFibreClosedChain`, but no matching theorem.
  A separate `rg` for `full_dimension_local_chain_contraction` across Mathlib,
  both project source trees, and the upstream-name index found no name clash.
  The consumer's complete statement/docstring was read; it concerns geometric
  specialization chains and is not a duplicate of this ring-theoretic theorem.

No statement fault, disputed assertion, new node, or dependency repair was found.
The first server `scompile.py` run passed both sandbox and library compilation
in 1.8 seconds each, with no unexpected warning or error.

## Second reading by Q80

A separate second pass by the assigned worker reread the complete node statement
and the delivered theorem; the dispatcher forbids starting another agent, and
the maintainer supplies the independent delivery review.

The rereading checked the hypotheses `[CommRing A] [IsDomain A]`, maximality of
`m`, the natural-valued `r`, and both dimension equalities against the node.
It checked that the localization is the recorded construction and contraction
is inverse image under its canonical map. It counted the `r + 1` vertices,
verified that primeness and `StrictMono` encode exactly the strict chain, and
checked both the existential chain clause and the separate universal clause.
Within the universal clause it matched primality, strictness, containment in
`m`, the zero endpoint, and the prescribed maximal endpoint. In particular the
endpoints are not properties of only the existential witness, and `Fin.last 0`
remains the same vertex as `0` in the singleton case. All variables and the
universe are explicit, with `autoImplicit false`. No mismatch was found and
no statement correction was necessary. The only postponed declaration is
`Ideal.full_dimension_local_chain_contraction`, whose proof is exactly `sorry`.
