## Worker report

The module `Sheaf.RingTheory.PositiveMonoidConvolutionLength` states
`AddMonoidAlgebra.positiveMonoid_convolution_length`, with its only proof `sorry`.
No new definitions, new nodes, dependency repairs, or statement corrections are needed.
Only the item's `lean` field changes. All universes and variables are explicitly bound.

Source read: ILO, Travaux de Gabber, Exposé VI, 1.6(i)–(ii), printed p. 70
(PDF p. 76). This supplies the formal monoid models, not the elementary coefficient
lemma; the node and Lean docstring correctly identify the latter as agent-supplied.
I also read the current blueprint's `lem-trf-local-term-locality` statement and proof
under `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`.
The node is an auxiliary lemma, not the unit's own statement.

Hypothesis and clause correspondence:

- Free finite-rank ambient group: `(G : Type u) [AddCommGroup G]
  [Module.Free ℤ G] [Module.Finite ℤ G]`. Over ℤ, free and finitely generated
  is precisely possession of a finite integral basis. The canonical ℤ-module
  on the additive group is used.
- Submonoid and its nonzero finite generator family: `(P : AddSubmonoid G)
  (s : ℕ) (g : Fin s → G)`, `hg : ∀ i, g i ≠ 0`, and
  `hgen : AddSubmonoid.closure (Set.range g) = P`. The closure equality also
  entails that every generator lies in P; it introduces no extra condition.
  `s = 0` is allowed.
- Integral homomorphism and positivity on P minus zero:
  `wgt : G →+ ℤ` and `hpos : ∀ p : P, p ≠ 0 → 0 < wgt (p : G)`.
- Every sum of l nonzero elements has positive weight when l > 0, and length
  bounded by weight: the first conjunct quantifies `l`, `f : Fin l → P`,
  and nonvanishing of every `f i`, then asserts both implications/inequalities.
  A decomposition of p is precisely such an f whose sum equals p.
- Attained maximum: `∃ ν : P → ℕ` and, for each p,
  `IsGreatest {l | ∃ f : Fin l → P, (∀ i, f i ≠ 0) ∧ (∑ i, f i) = p} (ν p)`.
  Membership in this set is part of `IsGreatest`, so attainment is explicit.
  The empty family is automatically allowed and has sum zero. `ν 0 = 0`
  is a separate conjunct.
- Finite bounded weights: `∀ M : ℤ, 0 ≤ M →
  Set.Finite {p : P | wgt (p : G) ≤ M}`.
- Finite low lengths: `∀ n : ℕ, 1 ≤ n → Set.Finite {p : P | ν p < n}`.
- Pair and triple finiteness: `Set.Finite {q : P × P | q.1 + q.2 = p}` and
  `Set.Finite {q : P × P × P | q.1 + q.2.1 + q.2.2 = p}` for every p.
- Arbitrary commutative coefficients: `∀ (A : Type v) [CommRing A]` follows
  the length and finiteness conclusions. There are no local, Noetherian,
  nontriviality, topology, or completeness assumptions on A.
- The literal coefficient space is `P → A`, with `∃ ring : CommRing (P → A)`.
  The explicit `ring.toZero`, `ring.toOne`, `ring.toAdd`, and `ring.toMul`
  in every formula ensure that its asserted multiplication is convolution.
  The four formulas specify the zero family, unit `Pi.single 0 1`, componentwise
  addition, and convolution `∑ᶠ q : {q : P × P // q.1 + q.2 = p},
  a q.1.1 * c q.1.2`. The index set was separately asserted finite, so this
  `finsum` is the ordinary finite sum, with no convergence convention needed.
- Monomials `z^p` are Mathlib's `Pi.single p (1 : A)`, whose value at q is
  1 when q = p and 0 otherwise. This does not define a second monomial notion.
- The map C is an actual `@RingHom A (P → A) _ ring.toNonAssocSemiring`.
  Its formula `C a p = if p = 0 then a else 0` is exactly `C(a) = a z^0`.
  Its type includes preservation of one, not just a nonunital homomorphism.
- The monomial product formula uses the explicit multiplication to assert
  `z^u z^v = z^(u+v)`. The next conjunct gives the coefficient of `C(a)z^p`
  at q as `if q = p then a else 0`.
- Shift: for every s₀ and c, `p = s₀ + q` implies that the coefficient of
  `z^s₀ c` at p equals `c q`; if no such q exists it is zero. The last
  conjunct explicitly asserts uniqueness by cancellation,
  `s₀ + q = s₀ + q' → q = q'`.

Dependency declarations used: the sole recorded statement dependency is
`def-weil-pbc-free-module`, whose `Mathlib.LinearAlgebra.FreeModule.Basic`
declaration `Module.Free` was read with its complete signature and docstring.
It is used directly. `Module.Finite` is the Mathlib class in
`Mathlib.RingTheory.Finiteness.Defs`; it supplies finite rank together with
freeness. Other existing notions are `AddSubmonoid` and its `closure`, `IsGreatest`,
`Set.Finite`, `Pi.single`, `RingHom`, and Mathlib's `finsum`.
There are no proof dependencies to import. No downstream coefficient module is
imported, so no dependency cycle is introduced.

Edge cases checked before writing:

- s = 0 gives P = {0}. Only length zero occurs; ν(0) = 0; every nonnegative
  bounded-weight set and every S_n for n ≥ 1 is a singleton. Pair and triple
  sets at zero are singletons, and the convolution ring identifies with A.
- The zero-rank ambient group is included by the free finite module hypotheses.
- l = 0 is allowed; the positivity implication has false premise and the
  inequality becomes 0 ≤ 0. A nonempty zero-sum decomposition is ruled out by
  positive integral weights.
- M = 0 leaves only zero; n = 1 leaves only zero since every nonzero p has
  its singleton decomposition. These boundary cases agree with the statement.
- The trivial coefficient ring is included; all monomial and constant formulas
  continue to hold when 1 = 0. No domain assumption is made.
- The shift at s₀ = 0 is the identity. If p has no residual exponent in P,
  its coefficient is zero. For the nonfree monoid generated by 2 and 3 in ℤ,
  at p = 3 and s₀ = 2 there is no residual exponent, whereas p = 5 has the
  unique residual exponent 3. No unique factorization of p is assumed.
- G and A have independent universes u and v; all P-indexed functions and
  finite sums are available at those universes.

Searches (2026-10-24; raw tool records in the sandbox searches.jsonl):

- LeanFinder via msearch.py, query "A finitely generated positive additive lattice
  monoid has finite weight sublevel sets and a commutative convolution ring on all
  coefficient functions": 8 hits, including `Finsupp.finite_of_nat_weight_le`,
  `Finsupp.le_weight`, Hahn-series finite-support results, and monoid-algebra
  finite-type results. None states this result on all functions on a possibly
  nonfree positive lattice submonoid.
- Loogle via msearch.py, query `Finset.HasAntidiagonal, Module.Free`: 0 hits.
- Mathlib grep via msearch.py, query `finite_of_nat_weight_le|convolution|HasAntidiagonal`
  in RingTheory: 25 hits, principally coalgebra/Hopf convolution and power-series
  antidiagonals. These do not give this general statement.
- LeanSearch via msearch.py, query "Positive finitely generated monoids have maximal
  decomposition lengths and finite convolution rings of coefficient functions":
  8 hits, principally `AddMonoid.FG`, fg characterizations, and monoid algebra
  finite-type results. No exact match.
- Direct rg of `convolution|positiveMonoid|PositiveMonoid|decompositionLength` in
  `lean/WeilConjectures` and `lean/Sheaf`, and grep of this node id in
  `lean/WeilConjectures`: no exact existing statement. The existing
  `Sheaf.RingTheory.FinitePatternFactorization` and
  `Sheaf.RingTheory.MonoidCompletionCoefficients` were read in full. They use
  the same explicit-ring/finsum interface but add local/Noetherian/completeness
  assumptions and prove different conclusions, so cannot replace this lemma.
- The proposed full declaration name was searched in Mathlib, both project roots,
  and `dag/lean_names_upstream.json`: no collision.

Validation: scompile.py compiled the delivered file cleanly on the server in both
sandbox and library-module modes (3.0 s and 1.5 s). No warnings or errors were
reported. The module has no line exceeding 100 characters.

No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q49

I reread the node and the completed Lean signature clause by clause after the clean
compile; the maintainer supplies the independent review after delivery. The finite
basis assumption is encoded as free plus finite over ℤ, and generator membership
is included in the closure equality. I checked that `IsGreatest` includes attainment,
that integer M and natural n have their stated lower bounds, and that triples use
all three coordinates of the right-associated product. I also checked each ring
operation against its explicitly bound structure: no pointwise multiplication on
`P → A` enters the conclusion. C is unital into that structure, and both branches
of the shift formula and cancellation uniqueness appear. The generator-empty and
coefficient-zero cases remain included. No mismatch or statement edit was found.
