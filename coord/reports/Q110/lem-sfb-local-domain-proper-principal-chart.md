## Worker report

Module `Sheaf.RingTheory.LocalDomainProperPrincipalChart` states
`IsLocalRing.exists_properPrincipalFractionChart`, with its entire proof `sorry`.
No definitions, dependency repairs, new nodes, or statement corrections are needed.
The node copy changes only `lean`. Its source is Stacks Project, algebra.tex,
Tag 00P8, `lemma-dominate-by-dimension-1`, the proof from the dominating valuation
ring through the construction of S and the properness of x_r S. I read that
source locally (lines 28892 onward); adjoining x_j/x_j = 1 in our formulation
does not change the source's chart, which omits that redundant generator.

Hypothesis and conclusion correspondence:

- Commutative Noetherian ring B: `(B : Type u) [CommRing B] [IsNoetherianRing B]`.
- Nonzero local integral domain: `[IsLocalRing B] [IsDomain B]`; the standard
  classes include nontriviality, and `IsLocalRing` gives the unique maximal ideal.
- Nonzero maximal ideal: `hm : maximalIdeal B ≠ ⊥`.
- Field K containing B and consisting of fractions b/c with c nonzero:
  `(K : Type v) [Field K] [Algebra B K] [IsFractionRing B K]`.
  `IsFractionRing` is localization at non-zero-divisors. In a domain these are
  exactly the nonzero elements; its algebra map is injective
  (`IsFractionRing.injective`). Thus it expresses the given inclusion and
  fraction condition, not an extra field-extension restriction. The two
  universes are independent.
- Integer r at least one: existential `r : ℕ` and `0 < r`.
- Finite family x_1,...,x_r: `x : Fin r → B` (zero-based indexing only).
- Each generator nonzero and in m_B:
  `∀ i : Fin r, x i ≠ 0 ∧ x i ∈ maximalIdeal B`.
- The family generates m_B: `Ideal.span (Set.range x) = maximalIdeal B`.
- An index j in that family: existential `j : Fin r`; a is rendered directly
  as `x j` throughout, without a hidden let or a separate assumption.
- The actual subring S of K consists of polynomial expressions in x_i/a over B:
  existential `S : Subalgebra B K` with
  `S = Algebra.adjoin B (Set.range (fun i : Fin r ↦
  algebraMap B K (x i) / algebraMap B K (x j)))`.
  Mathlib's `Algebra.adjoin` is the least subalgebra containing these elements,
  equivalently finite polynomial expressions; it includes all coefficients
  through the fixed algebra map. S is not an arbitrary finite-type chart.
- S Noetherian: `IsNoetherianRing S`.
- Extended maximal ideal equals aS:
  `Ideal.map (algebraMap B S) (maximalIdeal B) =
  Ideal.span {algebraMap B S (x j)}`.
  `Ideal.map` is by definition the ideal span of the image of the original ideal.
- aS is proper: `Ideal.span {algebraMap B S (x j)} ≠ ⊤`.
  The top ideal is the whole ring S. The principal generator is the canonical
  image of a in S and hence has underlying value algebraMap B K a in K.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`; read its docstring and definition and
  `isNoetherianRing_iff_ideal_fg`. Imported publicly for the statement.
- `def-weil-field`: Mathlib match `Field`, `Mathlib.Algebra.Field.Defs`;
  read its docstring and class signature. Publicly available through
  `Mathlib.RingTheory.Localization.FractionRing`.
- Proof dependency `lemma-nagata-local-domain-valuation-dominates`:
  `LocalSubring.exists_le_valuationSubring`,
  `Mathlib.RingTheory.Valuation.LocalSubring`, imported privately.
- Proof dependency `def-trf-valuation-ring`: `ValuationRing` and
  `ValuationRing.TFAE`, `Mathlib.RingTheory.Valuation.ValuationRing`,
  imported privately, with their signatures read.
- Proof dependency `lem-weil-pbc-finite-type-algebra-noetherian`:
  `Algebra.FiniteType.isNoetherianRing`, `Mathlib.RingTheory.FiniteType`,
  imported privately, with its signature read.

Additional standard interfaces are `IsFractionRing`, `Algebra.adjoin`,
`Subalgebra`, `Ideal.map`, `Ideal.span`, and `IsLocalRing.maximalIdeal`.
Their definitions were read; they require no private copies or new notions.
The theorem docstring carries all six proof steps and names their DAG uses.

Edge cases: the zero ring is excluded by the domain/local assumptions; a field
B is excluded exactly by hm. An empty generator family is ruled out by 0 < r
and j : Fin r. For r = 1 the quotient is x_0/x_0 = 1, so S is the image of B
and its already principal nonzero maximal ideal stays proper. Zero denominators
are excluded by the nonzero-generator condition and the injective fraction-field
map. No distinctness or minimality of the generators is required. No dimension,
characteristic, valuation-ring, or finite field-extension hypothesis was added.
The codomain field may live in any universe v, independently of u.

Searches made through the prescribed msearch.py Q110/item wrapper:

- LeanFinder: "A Noetherian local domain has generators of its nonzero maximal
  ideal and a fraction chart adjoining their quotients by one generator where
  the extended maximal ideal is proper principal". Eight hits, including
  `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`,
  `IsDiscreteValuationRing.TFAE`, and
  `exists_maximalIdeal_pow_eq_of_principal`: all concern rings already having
  valuation/Dedekind/principal properties, not existence of this chart.
- Loogle: `Algebra.adjoin, IsNoetherianRing`. One hit,
  `isNoetherian_adjoin_finset`, with an integrality hypothesis; it does not
  assert existence or properness of a chart.
- Mathlib grep: `adjoin.*(maximalIdeal|valuation)|principal.*chart|proper.*principal`
  in RingTheory. One hit, `LocalRing/Etale.lean`, unrelated to this assertion.
- LeanSearch: "A nonfield Noetherian local domain has a fraction chart in which
  the extended maximal ideal is proper and generated by a member of its finite
  generating set". Eight hits about fractional ideals, Dedekind domains, and
  existing principal maximal ideals; none states this existence theorem.
- `rg` in both live `lean/WeilConjectures` and `lean/Sheaf`, and the upstream
  name index, for principal charts, charts principal, adjoin/maximalIdeal, and
  the item id. Read `WeilConjectures/Blowup/Affine/Principalization.lean`:
  `map_awayAlgebraMap_eq_span_singleton` identifies extended ideals on an
  already specified homogeneous chart; it neither chooses a chart in a
  fraction field nor asserts its properness. No exact match found.
- Full proposed declaration-name search in Mathlib, WeilConjectures and Sheaf
  found no collision. No repair note exists for the item.

Validation: prescribed scompile.py compiled this file both as the sandbox
module and as `Sheaf.RingTheory.LocalDomainProperPrincipalChart`, exit code 0,
with no errors or unexpected warnings. All variables and universes are explicitly
bound. Line lengths are at most 100. No statement dispute or node fault found.

## Second reading by Q110

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
