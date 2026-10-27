## Worker report

The module `Sheaf.RingTheory.AdmissibleModificationValuativeRingReduction` states
`RingTheory.admissibleModification_valuative_ring_reduction`, with `sorry` as its
only proof. No definitions or auxiliary theorems are introduced. The node changes
only in `lean`; its statement, proof, dependencies and provenance are preserved.

Source checked directly: Illusie--Laszlo--Orgogozo, Travaux de Gabber,
XX 4.4, printed pp. 373--374 (PDF pages 379--380). The paragraph beginning
“Say I = (φ)” states that the localization is henselian local, with maximal ideal
corresponding to the intersection, and that the quotient is a henselian valuation
ring with the φ-adic valuation topology. The supplied DAG proof makes explicit
the local algebra and the canonical fraction-field identifications. The module
contains its ten proof steps, including the reciprocal-polynomial argument for
henselianity of the localization, in the theorem docstring.

Hypothesis and conclusion correspondence:

- The arbitrary nonzero commutative henselian local ring is `(B : Type u)
  [CommRing B] [HenselianLocalRing B]`. Mathlib's `HenselianLocalRing` extends
  `IsLocalRing`, which itself extends `Nontrivial`, so no nonzero hypothesis is lost.
- The element is `(φ : B)`; `hNonunit : ¬ IsUnit φ` and
  `hRegular : φ ∈ nonZeroDivisors B` are exactly the nonunit and nonzerodivisor
  hypotheses. No domain or Noetherian hypothesis is imposed on B.
- `hPrincipal` quantifies over every `J : Ideal B` with `J.FG` and
  `∃ n : ℕ, 1 ≤ n ∧ Ideal.span {φ ^ n} ≤ J`. Its conclusion
  `∃ d : B, d ∈ nonZeroDivisors B ∧ J = Ideal.span {d}` says precisely that
  each such ideal is principal with a regular generator. Containment of the
  principal ideal, rather than of an unspecified power of J, is used.
- `P : Ideal B` is fixed by `hP : P = ⨅ n : ℕ, Ideal.span {φ ^ (n + 1)}`.
  The shifted index enumerates exactly all positive powers, including the first;
  this equality only names the intersection in the node. It restricts no ring.
- `S` is the actual `Localization.Away φ`, and `V` is the actual quotient `B ⧸ P`.
  These are Mathlib constructions, not arbitrary rings or chosen models.
- The first existential asserts `P.IsPrime`. This supplies the quotient's
  `IsDomain` instance for the later `ValuationRing (B ⧸ P)` witness.
- The next witnesses are `HenselianLocalRing (Localization.Away φ)` and
  `HenselianLocalRing (B ⧸ P)`, and then `ValuationRing (B ⧸ P)`.
  These are conclusions, not assumptions. The maximal-ideal equality is
  `IsLocalRing.maximalIdeal (Localization.Away φ) =
  P.map (algebraMap B (Localization.Away φ))`, exactly the ideal PS.
- `Ideal.Quotient.mk P φ ≠ 0` and `¬ IsUnit (Ideal.Quotient.mk P φ)` render
  the nonzero and noninvertible image of φ in V.
- The first ring equivalence has source `S ⧸ P.map (algebraMap B S)` and
  target `Localization.Away (Ideal.Quotient.mk P φ)`. Its compatibility is
  required on EVERY `s : S`: after the quotient map it equals
  `IsLocalization.Away.map S ... (Ideal.Quotient.mk P) φ s`. This is precisely
  the localized canonical quotient map, not an arbitrary identification.
- The second equivalence identifies that same localization with
  `FractionRing (B ⧸ P)`. It commutes with the canonical algebra maps on
  EVERY `x : B ⧸ P`. This specifies the canonical fraction-field identification;
  the prime witness ensures Mathlib's fraction ring here is a field. The
  composite equivalence gives the asserted canonical identification S/PS = Frac(V).
- The final `Filter.HasBasis` is at zero for the explicitly supplied topology
  `((ValuationRing.valuation V (FractionRing V)).comap
  (algebraMap V (FractionRing V))).subgroups_basis.topology`.
  Its indices satisfy `1 ≤ n` and its sets are exactly
  `(Ideal.span {Ideal.Quotient.mk P φ ^ n} : Set V)`. This is the topology of
  the canonical valuation on Frac(V), restricted to V, not an existentially
  chosen topology. Mathlib uses multiplicative values with zero; its strict
  balls `v(x) < γ` are exactly the node's additive balls `v(x) > γ` after
  reversing order and converting multiplication into addition. In both
  conventions zero belongs to every ball. `Valuation.subgroups_basis` supplies
  the valuation topology directly, and `HasBasis` expresses BOTH that the
  displayed ideals are neighborhoods and that each neighborhood contains one.

Dependency declarations read and used:

- `def-weil-pbc-henselian-terminology`: recorded module
  `WeilConjectures.Mathlib.RingTheory.Henselian` is publicly imported. Its
  docstring identifies the local-ring notion as Mathlib's `HenselianLocalRing`
  (`Mathlib.RingTheory.Henselian`, full class signature read). The dependency's
  `IsStrictlyHenselianLocalRing` class was also read; strictness is not required.
- `def-trf-valuation-ring`: the recorded Mathlib match is
  `ValuationRing` and `ValuationRing.TFAE` in
  `Mathlib.RingTheory.Valuation.ValuationRing`. Their signatures and the
  fraction-field equivalent condition were read. This module is publicly
  imported; the class is used without creating another valuation-ring notion.
  Its actual canonical `ValuationRing.ValueGroup` and `ValuationRing.valuation`
  constructions are used by the topology clause.
- Proof imports, without `public`: `WeilConjectures.RingTheory.IntegralOverHenselianPair`
  (`henselianRing_of_isIntegral`) and
  `WeilConjectures.RingTheory.HenselianLocalRootLifting`
  (`IsLocalRing.idempotent_lifting_iff_monic_simple_root_lifting`). Both
  declarations and their proof docstrings were read. They are precisely the
  two non-elementary proof dependencies recorded in the node.
- The other public imports are Mathlib's `RingTheory.Localization.Away.Basic`
  (actual localization and its canonical `IsLocalization.Away.map`) and
  `Topology.Algebra.Valued.ValuationTopology` (the actual valuation topology).

Edge cases checked before writing:

- The zero ring is excluded exactly by the henselian local-ring assumption.
  In a field, there is no regular nonunit, so the hypotheses have no instances;
  φ = 0 and all nilpotent φ are likewise excluded by regularity and nontriviality.
- P may be zero or nonzero; no separatedness assumption is inserted. B may
  have zero divisors in P. The conclusion asserts domain structure only on V.
- When P = 0 (for example a henselian valuation domain with a suitable cofinal
  positive element), S is its field of fractions, and PS = 0 is its maximal ideal.
- The unit ideal is among the finitely generated admissible ideals and has the
  regular generator 1; zero cannot be admissible because φ is regular.
- The basis includes every positive integer; no discrete valuation, rank-one,
  Noetherian, finite-dimensional, completion or excellence hypothesis is added.
  The intrinsic value group allows non-discrete and higher-rank cases whenever
  the given element's positive multiples are cofinal, as proved in the node.
- `universe u` is explicit; all variables are explicitly bound. Localization,
  quotient, fraction field and value group preserve the ring's universe.

Searches for an existing statement (all performed read-only):

- `msearch.py ... leanfinder` with query “Henselian local ring with all finitely
  generated ideals containing a power of a regular element principal:
  localization henselian and separated quotient valuation ring” returned eight
  general henselian-ring declarations: `HenselianLocalRing`, its local-ring
  projection, `instHenselianRingMaximalIdeal`, `Field.henselian`,
  `HenselianLocalRing.TFAE`, `HenselianRing`, `IsAdicComplete.henselianRing`,
  and `HenselianLocalRing.is_henselian`. None gives this statement.
- `msearch.py ... loogle "HenselianLocalRing, ValuationRing"`: zero hits.
- `msearch.py ... grep "henselian.*[Ll]ocaliz|[Ll]ocaliz.*henselian" RingTheory`:
  zero hits in Mathlib. A direct Mathlib search and upstream-name-table search
  found no matching statement or conflicting chosen declaration name.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id, henselian
  localization and intersections of principal powers found no statement of
  this lemma. Upstream `IsLocalRing.isPrime_iInf_span_pow` and the discrete
  valuation-ring quotient lemmas instead assume a principal maximal ideal,
  a special case not covering this node. General localizations in other
  henselian/pro-etale modules do not provide this admissible-ideal result.
- Read Mathlib `ValuationRing.valuation`, `Valuation.comap`,
  `Valuation.subgroups_basis`, `IsLocalization.Away.map`, `FractionRing.field`,
  and the quotient-domain instance to ground the canonical constructions.

Validation: `scompile.py Q17 lem-per-admissible-modification-valuative-ring-reduction
<module>` compiled both the sandbox and library-name versions successfully
(2.3 s and 1.9 s), with no errors or warnings. No statement correction,
new node, dependency repair or statement dispute is needed.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
