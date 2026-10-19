## Worker report

The module `Sheaf.RingTheory.OneDimensionalComponentConormal` states
`Ideal.exists_pow_conormal_torsion_of_one_dimensional_component`, with its entire proof
postponed by `sorry`. No definition, auxiliary theorem, new node, dependency repair, or
statement correction is needed. The node changes only in `lean`.

Source read: `literature/stacks-project/more-algebra.tex`, Tag 0AW3,
`lemma-not-formally-catenary`, the d = 1 paragraph, lines 32325 onward. The node extracts
exactly the two conormal assertions of that paragraph; it does not assert that the
associated-prime set is nonempty. The declaration docstring carries the node's four-step
proof, including the support calculation and the zero-conormal case.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| A commutative Noetherian local domain | `{A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]` |
| m is its maximal ideal | `IsLocalRing.maximalIdeal A` |
| B is the maximal-ideal completion, with its canonical A-algebra map | `AdicCompletion (IsLocalRing.maximalIdeal A) A` and `algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)` |
| q is a minimal prime of B | `(q : Ideal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) [q.IsPrime]` and `hq : q ∈ minimalPrimes (AdicCompletion (IsLocalRing.maximalIdeal A) A)`; the prime instance is already entailed by minimal-prime membership |
| dim(B/q) = 1 | `hdim : ringKrullDim ((AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ q) = 1` |
| There exist integers n,c >= 1 | `∃ n c : ℕ, 1 ≤ n ∧ 1 ≤ c ∧ ...`; natural positive exponents are exactly the positive integers here |
| J = q^n | The same ideal `q ^ n` is substituted in both conclusions, avoiding a separate existential J or a let binder |
| JB_q = 0 | `(q ^ n).map (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal A) A) (Localization.AtPrime q)) = ⊥` |
| J/J² as a B-module | `(q ^ n).Cotangent`, Mathlib's actual quotient of J by `J • ⊤ : Submodule B J`; its image in B is J², as `Ideal.map_toCotangent_ker` confirms |
| (mB)^c (J/J²) = 0 | The c-th power of `(IsLocalRing.maximalIdeal A).map (algebraMap A B)` is contained in `Module.annihilator B (q ^ n).Cotangent` |

All variables and the universe `u` are explicit; `autoImplicit` is false. The completion,
quotient, and localization live in the universe of A, so this does not restrict any ring
allowed by the node. No extra ring B or arbitrary ring map is supplied as a hypothesis.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (all ideals finitely generated).
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`; the public import of `.Algebra` supplies its ring and algebra structures.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`, using `WithBot ℕ∞` and the genuine prime-ideal chain dimension.
- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime`, the actual localization at q's complement.
- The existing Mathlib notion `Ideal.Cotangent` from
  `Mathlib.RingTheory.Ideal.Cotangent` renders J/J² without redefining it.
- The existing `minimalPrimes` from `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`
  renders minimality, without replacing it by a dimension condition.

The following already recorded proof dependencies are imported non-publicly, following
the node's proof plan: `AdicCompletion.isNoetherianRing` from
`WeilConjectures.RingTheory.AdicCompletionNoetherian` (read via `scompile.py --source`);
`AdicCompletion.maximalIdeal_eq_map` and the local-completion instance from
`Mathlib.RingTheory.AdicCompletion.LocalRing`; `IsLocalization.isNoetherianRing` from
`Mathlib.RingTheory.Localization.Submodule`;
`IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes` from
`Mathlib.RingTheory.Ideal.MinimalPrime.Localization`;
`Ideal.exists_pow_le_of_le_radical_of_fg` from `Mathlib.RingTheory.Finiteness.Ideal`;
`Module.mem_support_iff_of_finite` and `Module.support_eq_zeroLocus` from
`Mathlib.RingTheory.Support`; `PrimeSpectrum.zeroLocus_eq_iff` from
`Mathlib.RingTheory.Spectrum.Prime.Topology`; and `Ideal.radical_eq_sInf` from
`Mathlib.RingTheory.Ideal.Operations`. No dependency record is replaced.

Edge cases checked before writing:

- If q = 0, then J = 0 for every positive n, so both conclusions hold, with c = 1.
  This covers a one-dimensional domain completion such as a complete DVR.
- If A is a field, its completion is A and its minimal-prime quotient has dimension zero.
  Thus the dimension-one premise excludes it for the mathematical reason, not by an
  extra positive-dimensionality assumption.
- A nonreduced completion is allowed; it is not assumed to be a domain. Nilpotence in
  B_q can require n > 1. The ring k[[t,e]]/(e²), with q = (e), illustrates the local
  calculation: n = 2 makes J zero.
- Multiple components cause no restriction: in k[[x,y]]/(xy), q = (x) has zero extension
  at q and its conormal is killed by the closed-point ideal. Only B/q must have
  dimension one; no equidimensionality assumption on B is present.
- When J/J² = 0 its annihilator is the unit ideal, so the second conclusion still holds.
  The statement does not require nonempty support or nonempty associated primes.
- n = 0 and c = 0 are explicitly excluded as in the node.

Searches for an existing statement:

The prescribed msearch.py wrapper was used with group Q93 and this item. The persistent
search log is `searches.jsonl` in the sandbox. Exact queries and results for this pass:

- `grep`: `conormal|Cotangent.*annihilator|annihilator.*Cotangent|pow.*minimalPrimes` in `RingTheory`. Result: 2 hits; `Mathlib/RingTheory/Extension/Cotangent/Basic.lean`, `Mathlib/RingTheory/Extension/Cotangent/Basic.lean`. No exact two-conclusion theorem.
- `loogle`: `"Ideal.Cotangent", "pow"`. Result: 0 hits; . No exact two-conclusion theorem.
- `leanfinder`: `A positive power of a minimal prime with one dimensional quotient in a Noetherian local completion has zero localization and conormal annihilated by a maximal ideal power`. Result: 8 hits; `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`, `IsHausdorff.of_isLocalRing`, `Algebra.IsSmoothAt`, `instIsHausdorffMaximalIdeal`, `ringKrullDim_le_ringKrullDim_quotSMulTop_succ`, `exists_maximalIdeal_pow_eq_of_principal`, `Ideal.iInf_pow_eq_bot_of_isLocalRing`, `isReduced_ofLocalizationMaximal`. No exact two-conclusion theorem.
- `leansearch`: `A minimal prime with one dimensional quotient has a positive power whose localization is zero and whose conormal is killed by a maximal ideal power`. Result: 8 hits; `Ideal.map_height_le_one_of_mem_minimalPrimes`, `Ring.KrullDimLE.of_isLocalization`, `Ring.KrullDimLE.minimalPrimes_eq_setOf_isMaximal`, `IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing`, `Ideal.minimalPrimes_eq_subsingleton_self`, `Ring.KrullDimLE.minimalPrimes_eq_setOf_isPrime`, `Ideal.primeHeight_eq_zero_iff`, `IsLocalization.minimalPrimes_map`. No exact two-conclusion theorem.

Direct ripgrep searches in Mathlib found `Ideal.Cotangent` and its defining quotient,
so no private conormal definition was introduced. Searches for the node id and for
`one_dimensional_component_conormal`, `OneDimensionalComponentConormal`, and
`exists_pow_conormal_torsion` in the upstream `WeilConjectures` tree, `lean/Sheaf`, and
`dag/lean_names_upstream.json` found no existing theorem with this name or statement.
The broader project conormal search found related results about presentations and smoothness,
and the parent's proof citation in `RatliffFormalCatenarity`, but no match for this lemma.
Loogle returned no result for `"Ideal.Cotangent", "pow"`; semantic results concern
intersection of powers, dimension-zero localizations, or principal maximal ideals.

Validation: the required `scompile.py Q93 lem-per-one-dimensional-component-conormal
<module>` succeeded both in its sandbox check (2.4 s) and its library-name check (2.1 s),
with no errors or warnings. An interrupted earlier compile lost its PTY session; no
compiler process was left running before the recorded successful rerun.

No STATEMENT-DISPUTED flag or node fault was found. Independent statement review remains
with the maintainer, as specified by the dispatch brief.

## Second reading by Q93

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
