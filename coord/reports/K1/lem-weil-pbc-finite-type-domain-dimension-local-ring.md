## Worker report

The module `Sheaf.RingTheory.FiniteTypeDomainDimensionLocalRing` states
`finiteTypeDomain_ringKrullDim_localizationAtMaximal`. It binds a field `k`, a commutative
ring `S`, an `Algebra k S`, finite type structure, and domain structure. Its first clause
quantifies every maximal ideal `m` (represented by the typeclass `[m.IsMaximal]`) and
states `ringKrullDim (Localization.AtPrime m) = ringKrullDim S`, rendering the localization
at the maximal ideal. Its second clause supplies a natural number `d` with
`ringKrullDim S = (d : WithBot ℕ∞)` and says every `LTSeries` of primes whose range is
`IsMaxChain` for inclusion has `p.length = d`; this is the maximal-chain formulation.
The proof is `sorry`, as required for stage 2.

The dependency declarations used are `Algebra.FiniteType` from
`Mathlib.RingTheory.FiniteType`, `Localization.AtPrime` from
`Mathlib.RingTheory.Localization.AtPrime.Basic`, and `ringKrullDim` from
`Mathlib.RingTheory.KrullDimension.Basic`. These are exactly the recorded Mathlib
matches for `def-weil-pbc-finite-type-algebra`, `def-weil-pbc-localization-at-prime`,
and `def-weil-pbc-krull-dimension-ring` respectively.

Edge cases checked: the quantification over `d : ℕ` explicitly excludes negative
finite dimensions while allowing the zero-dimensional case; `IsDomain S` excludes the
zero ring as in the source; no nonempty or positive-dimension hypothesis is added; and
`LTSeries` permits length zero, covering maximal chains consisting of one prime.
The universe binders `u` and `v` are explicit and all variables are bound.

Searches made before writing: the node's recorded LeanSearch, LeanFinder, Loogle, and
Mathlib/source grep searches (all report no exact theorem); `rg` over the project and
`WeilConjectures` for finite-type dimension and the node id (no existing declaration).
The module compiled cleanly with `scompile.py` (the expected `sorry` warning is disabled).

## Earlier second reading (a previous round; superseded)

I reread the node and the compiled declaration clause by clause. The field and algebra
hypotheses are the explicit `k`, `S`, `Field`, `CommRing`, and `Algebra` binders; finite
type and domain are the two typeclass hypotheses. The first conclusion quantifies a
maximal ideal through `[m.IsMaximal]` and uses `Localization.AtPrime m`, exactly the
recorded localization notion. The second conclusion gives a natural finite dimension
and uses `LTSeries` plus `IsMaxChain` to render the stated maximal prime-chain clause.
No hypothesis or edge case from the node was omitted. The only adjustment after this
reading was recording the signature without the proof introducer, as required by the
node-field preflight.

## Second reading by K1

Read the sandbox node and module independently against Stacks Algebra Tag 00OS,
`lemma-dimension-spell-it-out`, its full statement and proof, and the adjacent
00OQ/00OR statements. The recorded literature path is absent on this machine;
the available Stacks checkout `/home/ubuntu/c1-stacks-review/algebra.tex` contains
these passages at lines 27723–27785, and its `tags/tags` maps all three tags to
the recorded labels. There are no additional standing hypotheses in this source.

Object/hypothesis/conclusion checklist (all pass):

- Field k: `{k : Type u} [Field k]`. Arbitrary characteristic, no algebraic closure
  or cardinality assumption.
- Commutative k-algebra S: `{S : Type v} [CommRing S] [Algebra k S]`.
  These are precisely the source objects, with independent explicit universes.
- Finite type: `[Algebra.FiniteType k S]`. Opened dependency
  `def-weil-pbc-finite-type-algebra` and Mathlib `RingTheory/FiniteType.lean`:
  the class asserts finite generation of the top subalgebra, exactly the node's
  equivalent generator formulation. No finite-module hypothesis is substituted.
- Integral domain: `[IsDomain S]`. In particular S is nonzero, as in the source;
  no Noetherian or local-ring assumption is added.
- Every maximal ideal m: `∀ (m : Ideal S) [m.IsMaximal]`. The instance binder is
  universal quantification over proofs of maximality, not an extra assumption
  on S. Maximality supplies primality required by localization.
- The actual local ring S_m: `Localization.AtPrime m`. Opened dependency
  `def-weil-pbc-localization-at-prime` and the Mathlib abbreviation in
  `Localization/AtPrime/Basic.lean`: localization at `m.primeCompl`, not a
  localization away from a single element or an arbitrary local algebra.
- Local dimension equals ring dimension:
  `ringKrullDim (Localization.AtPrime m) = ringKrullDim S`.
  Opened dependency `def-weil-pbc-krull-dimension-ring` and both
  `RingTheory/KrullDimension/Basic.lean` and `Order/KrullDimension.lean`:
  this is the supremum of strict prime-chain lengths in `WithBot ℕ∞`.
- The common dimension is a nonnegative integer:
  `∃ (d : ℕ), ringKrullDim S = (d : WithBot ℕ∞)`. This excludes both infinities
  and shares the same d with the following chain clause.
- Every maximal prime chain has that length:
  `∀ (p : LTSeries (PrimeSpectrum S)),
  IsMaxChain (fun q r : PrimeSpectrum S ↦ q ≤ r) (Set.range p) → p.length = d`.
  Opened `RelSeries`, `LTSeries`, `IsChain`, `IsMaxChain`, and the
  `PrimeSpectrum` partial order. The order is inclusion of the underlying
  ideals; the series has `length + 1` entries with strict adjacent inclusions.
  Maximality is no larger chain containing its range, exactly equivalent for
  this finite series to no insertion before, between, or after its entries.
  The node presents an equivalent formulation; stating both true conclusions
  together does not add an independent condition or weaken either clause.

Edge cases: length zero is represented by a singleton `LTSeries`, so a field
and dimension zero are included. The zero ring and empty spectrum are excluded
by the source's domain hypothesis, not by a new restriction. There is no
auxiliary indexing set or n binder restricting polynomial presentations;
zero generators are allowed by `Algebra.FiniteType`. No scheme hypotheses
occur. All characteristics and independent carrier universes u/v are covered;
there is no quantification over a potentially empty universe of test algebras.
All variables and universes in the unchanged signature are explicitly bound.

Independent searches (different wording from the worker):

- `msearch.py ... leanfinder "affine integral algebra over a field all saturated
  prime chains have equal length and all closed points have full dimension"`:
  eight hits, including `Ring.krullDimLE_of_isLocalization_maximal`, localization
  dimension bounds and integral-spectrum facts; none states both node clauses.
- `msearch.py ... loogle "Algebra.FiniteType, ringKrullDim"`: zero hits.
- `msearch.py ... leansearch "dimension of affine domain at every closed point
  and lengths of saturated maximal prime chains"`: service unavailable (Internal
  Server Error); no negative mathematical verdict inferred from this failure.
  LeanFinder, Loogle and direct source searches remain available.
- `rg` for `catenar|Catenar|equicodim|IsMaxChain`, the proposed declaration name,
  and dimension/localization combinations over Mathlib RingTheory, the full
  `WeilConjectures` tree and repository `lean/Sheaf`: no exact existing statement.
  Read the nearby project `maximal_chain_length_eq_of_depth` (requires a
  Cohen–Macaulay local ring), `topologicalKrullDimAt_eq_ringKrullDim_add_trdeg`
  (different pointwise formula), and upstream
  `ringKrullDim_eq_of_isLocalization_away` (single-element localization, no
  maximal-chain clause). None can replace this delivery with `existing: true`.

Mismatch repaired: H8, the original proof docstring compressed six DAG steps
into one paragraph and a dependency list. Expanded it to six numbered steps,
including the bound, maximal-ideal height, attained chain, prime correspondence,
common dimension and converse chain formulation, with the actual dependency
node ids at their uses. The theorem signature and node's `lean.statement` are
unchanged and verbatim equal. No definition is introduced, no proof is supplied:
the only declaration remains a theorem with `by sorry`. No new nodes, dependency
modules, or statement correction are needed. Header, source, blueprint id,
imports and line lengths satisfy the conventions.
