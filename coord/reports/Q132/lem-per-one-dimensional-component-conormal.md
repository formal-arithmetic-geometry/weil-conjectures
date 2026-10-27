## Worker report

The module `Sheaf.RingTheory.OneDimensionalComponentConormal` states
`AdicCompletion.exists_pow_minimalPrime_localization_eq_bot_and_cotangent_annihilated`.
Its only proof is `sorry`; there are no new definitions. The node is unchanged except
for its `lean` record. No new nodes, dependency modules, or statement corrections are needed.

Source read: `literature/stacks-project/more-algebra.tex`, Tag 0AW3,
`lemma-not-formally-catenary`, lines 32325--32358, especially the dimension-one
paragraph beginning at line 32342. The node extracts the two conormal assertions from
that paragraph; its proof expands the support argument and includes zero conormal modules.

Hypothesis and clause correspondence (write B for the completion in this report only):

- A commutative Noetherian local domain: `(A : Type u) [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]`.
- Its maximal ideal m: `IsLocalRing.maximalIdeal A`.
- B is exactly the m-adic completion: `AdicCompletion (IsLocalRing.maximalIdeal A) A`,
  rather than an arbitrary complete algebra or an additional hypothesis about B.
- q is a minimal prime of B: `q : Ideal B`, `[q.IsPrime]`, and
  `hq : q ∈ minimalPrimes B`. The prime instance repeats the primeness already in
  minimality so the standard localization type can be formed; it imposes no restriction.
- The component has dimension one: `hdim : ringKrullDim (B ⧸ q) = 1`.
- Integers n,c at least one: `∃ n c : ℕ, 1 ≤ n ∧ 1 ≤ c ∧ ...`.
  Positive natural numbers and positive integers give the same ideal powers.
- J is q^n: every occurrence of J is written directly as `q ^ n`.
- JB_q = 0: `(q ^ n).map (algebraMap B (Localization.AtPrime q)) = ⊥`.
  `Ideal.map` is extension of ideals along the canonical localization map.
- mB is `(IsLocalRing.maximalIdeal A).map (algebraMap A B)`.
- J/J² as a B-module is `(q ^ n).Cotangent`, Mathlib's quotient of J by
  `J • ⊤ : Submodule B J`. `Ideal.map_toCotangent_ker` identifies that denominator,
  after inclusion in B, with J²; `Ideal.toCotangent_eq_zero` gives the same kernel test.
- (mB)^c kills J/J²: `(mB)^c ≤ Module.annihilator B (q ^ n).Cotangent`.
  This ideal containment says exactly that every element of the ideal annihilates
  every element of the module; it makes no extra finiteness or nonzero-module assumption.

Statement dependencies used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, whose definition and ideal-finiteness equivalence were read.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`; its full compatible-sequence definition at line 171 was read.
  `Mathlib.RingTheory.AdicCompletion.Algebra` supplies the ring and canonical A-algebra
  structures on that same completion and is the public import used here.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`, with codomain `WithBot ℕ∞`, and its spectrum-chain definition.
- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime`, the localization at `q.primeCompl` with its canonical algebra map.

Additional standard notions use `minimalPrimes` from
`Mathlib.RingTheory.Ideal.MinimalPrime.Basic` and `Ideal.Cotangent` from
`Mathlib.RingTheory.Ideal.Cotangent`; their definitions and docstrings were read.
They implement notions already described in the item's own text, without a private copy.

All stated proof dependencies are imported as proof-only imports:

- `WeilConjectures.RingTheory.AdicCompletionNoetherian`:
  `AdicCompletion.isNoetherianRing` (completion Noetherianity).
- `Mathlib.RingTheory.AdicCompletion.LocalRing`: the completion's local-ring instance
  and `AdicCompletion.maximalIdeal_eq_map`.
- `Mathlib.RingTheory.Finiteness.Ideal`:
  `Ideal.exists_pow_le_of_le_radical_of_fg` (used twice in the proof sketch).
- `Mathlib.RingTheory.Support`: `Module.mem_support_iff_of_finite` and
  `Module.support_eq_zeroLocus`.
- `Mathlib.RingTheory.Localization.Submodule`: `IsLocalization.isNoetherianRing`.
- `Mathlib.RingTheory.Ideal.MinimalPrime.Localization`:
  `IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`.
- `Mathlib.RingTheory.Spectrum.Prime.Topology`: `PrimeSpectrum.zeroLocus_eq_iff`;
  its ideal-operations imports also expose the intersection-of-primes radical identity.

Edge cases checked before writing:

- If B is a domain and q = 0, n = c = 1 works and the conormal is zero.
- If q is nilpotent, a power J can be zero; the statement permits this and the
  annihilator of the zero module is the whole ring. No nonempty support is assumed.
- The zero ring is excluded by the local-domain hypothesis. If A is a field, its
  completion cannot have a dimension-one component; the conditional theorem remains correct.
- A minimal prime may be nonzero and B need not be a domain. No domain instance on B
  is imposed. The localization uses q, while the conormal is over B, not over B/q.
- Positive powers are required for both exponents; neither exponent is silently allowed zero.
- The universe u is explicit, as are all variables; `autoImplicit` is disabled.

Searches run on 2026-10-24 using the prescribed msearch wrapper:

- LeanFinder: "A power of a minimal prime in the completion of a Noetherian local
  domain with one dimensional quotient has zero localization and conormal module
  annihilated by a power of the maximal ideal". Eight hits, including DVR characterizations,
  `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`, and finite-dimensional cotangent spaces;
  no theorem giving this node's two conclusions.
- Loogle: `"Ideal.Cotangent", "pow"`. Zero hits.
- Mathlib grep in RingTheory:
  `conormal|Cotangent.*annihilator|annihilator.*Cotangent`. Two explanatory hits in
  `Mathlib/RingTheory/Extension/Cotangent/Basic.lean`, neither this theorem.
- LeanSearch: "A power of a minimal prime with one dimensional quotient in a
  Noetherian local ring has conormal module killed by a power of the maximal ideal".
  Eight hits, including Artinian quotients, maximal-ideal-power bounds and cotangent
  generation tests; none states the requested conclusion with vanishing at q.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for conormal and annihilator
  patterns found general conormal constructions, no matching component theorem.
  The narrower searches `one_dimensional.*conormal|conormal.*one_dimensional|`
  `one-dimensional completed|one-dimensional.*conormal` and
  `Cotangent.*annihilator|annihilator.*Cotangent` found no match.
- Exact node-id grep of `lean/WeilConjectures` and the upstream-name index found no match.
- Mathlib source grep found `Ideal.Cotangent` in `RingTheory/Ideal/Cotangent.lean:42`;
  its definition and kernel lemmas give exactly the quotient needed here.

Validation: scompile.py compiled the delivered file in sandbox and library module modes
with no errors or unexpected warnings (3.2 s and 6.2 s respectively).
The full four-step natural-language proof is in the theorem docstring.

## Second reading by Q132

This is the dispatcher's worker self-check; independent review belongs to the maintainer.
I reopened the node statement and the written theorem and matched the local-domain,
completion, minimal-prime, and dimension-one hypotheses against the binders above.
The conclusion quantifies over two positive exponents with the same n in the localized
ideal and conormal, and the same canonical completion algebra map in mB. In particular,
the module is the quotient of q^n by (q^n)², not B/q, q/q², or q^n/q^(n+1).
The localized ideal is an extension along B → B_q, not a kernel chosen as J.
Containment in the annihilator includes the zero-conormal case. The separate q.IsPrime
instance is logically supplied by minimality and is only needed to type Mathlib's
localization. No mismatch or statement correction was found; no change was required
after this reading. There are no new definitions or dependency modules to audit.
