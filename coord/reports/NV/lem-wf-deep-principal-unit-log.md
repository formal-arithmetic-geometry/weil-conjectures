## Worker report

The module `Sheaf.NumberTheory.Padics.DeepPrincipalUnitLog` states
`Padic.deepPrincipalUnit_log_exp`. Its only theorem proof is `sorry`; no definitions,
instances, axioms, or auxiliary theorems are introduced. The natural-language node statement
is unchanged. The already landed definition node `sk-d-real-log` is added to `stmt_deps`
so that the existing logarithm series is reused. I checked that this dependency has no
statement/proof dependency path back to this item.

Hypotheses and objects, matched individually:

- The prime ℓ is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A finite extension E/Q_ℓ is `(E : Type u) [Field E] [Algebra (Padic ℓ) E]
  [FiniteDimensional (Padic ℓ) E]`, with unrestricted explicit universe `u`.
- The valuation ring, maximal ideal and uniformizer are the recorded
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionMaximalIdeal` and
  `Padic.coefficientExtensionUniformizer`. There is no replacement ring or valuation.
- Normalization `v_E(𝔪_E)=1` and the abbreviation `e=v_E(ℓ)` are rendered by `(e : ℕ)`
  and `_he`, which says that ℓ is an integral unit times the recorded uniformizer to
  the power e. In a DVR this is exactly the normalized valuation of this nonzero
  integral element. Every finite extension supplies its unique such e, so this is
  a specification of the node's e, not a restriction on E or an extra structure.
- The depth is genuinely `(r : ℤ)`. `_hr` is the strict comparison
  `(e : ℚ) / ((ℓ : ℚ) - 1) < (r : ℚ)`. As e is nonnegative and ℓ is prime, this
  implies r > 0. Consequently taking the natural ideal power `r.toNat` loses no
  permitted integer depth. The decomposition also forces e > 0 since ℓ is not an
  integral unit. No extra positivity assumptions are imposed.
- Elements of `𝔪_E^r` are the subtype `↥((coefficientExtensionMaximalIdeal ℓ E) ^
  r.toNat)`. Coercions `(x : E)` pass through the actual recorded integer subring.

Each conclusion clause:

1. The first universal conjunct gives `HasSum` for the logarithm series and for
   the exponential series at every element of `𝔪_E^r`. The logarithm is reindexed
   by n ↦ n+1, with sign `(-1)^n`, exactly the node's `(-1)^(n+1)` at positive
   degree. The exponential includes n=0 and uses `Nat.factorial n` in E.
   The specified logarithmic limit is the existing
   `coefficientExtensionSmallLog ℓ E (x : E)`. Its argument is x and its value
   means log(1+x), as documented in its source.
2. The existential `exp : E → E` is specified by that exponential `HasSum` on
   the entire required domain. Since the field is Hausdorff this uniquely
   specifies the restricted exponential; its irrelevant values outside the
   stated domain are unconstrained. This is a conclusion characterizing the
   canonical series map, not an arbitrary assumed map or choice-based definition.
3. Both `ContinuousOn` conjuncts explicitly use the topology of
   `spectralNorm.normedField (Padic ℓ) E`. Their domain is the image of the ideal
   subtype in E. This is continuity of exp on the ideal and of x ↦ log(1+x)
   on the ideal. Translation u ↦ u−1 is a homeomorphism from 1+𝔪_E^r to 𝔪_E^r,
   so the latter is exactly the asserted continuity of log on principal units.
   All `HasSum` clauses use this same topology explicitly, with the unconditional
   summation filter. In this complete nonarchimedean field convergence of these
   series is unconditional, so this is the displayed power-series convergence.
4. The next universal conjunct gives membership of log(1+x) in the same ideal
   using an explicit witness y, followed by `exp(log(1+x)) = 1+x`.
5. The following conjunct gives `exp(x) = 1+y` for y in the same ideal and
   `log(exp(x)) = x`, written `coefficientExtensionSmallLog ℓ E (exp x - 1) = x`.
   Thus both restricted maps have the stated domains and codomains and are inverse.
6. The logarithm group law is stated for all x,y in the ideal as
   `smallLog ((1+x)*(1+y)-1) = smallLog x + smallLog y`. Ideal closure ensures
   `(1+x)*(1+y)` is again in 1+𝔪_E^r. The exponential group law is explicitly
   `exp (x+y) = exp x * exp y` on that same ideal. Together with the inverse
   identities these are precisely the mutually inverse homomorphisms. Their
   exponential values are units: exp(0)=1 follows from its series, and the group
   law at x,−x gives exp(x)exp(−x)=1. No extra unit hypothesis is needed.
7. Finally `∃ N : ℕ, 1 ≤ N ∧ ∀ u : (coefficientExtensionIntegers ℓ E)ˣ, ...`
   states one positive integer exponent for all integral units, and the conclusion
   `(u : O)^N - 1 ∈ 𝔪_E^r` is exactly `u^N ∈ 1+𝔪_E^r`.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, recorded declaration
  `Padic.finite_coefficientExtensionRing`, publicly imports
  `Sheaf.NumberTheory.Padics.CoefficientExtension`. I read the complete source and
  docstrings for its integer ring, maximal ideal, uniformizer and spectral absolute
  value. Those are selected by the uniquely specifying clauses of
  `Padic.extension_integers_dvr` in
  `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`, whose full signature was read.
- The added landed node `sk-d-real-log` records
  `Sheaf.NumberTheory.Padics.CoefficientExtensionSmallLog`,
  `Padic.coefficientExtensionSmallLog` (and `coefficientExtensionSmallUnits`). I read
  its full source locally and through `scompile.py --source`. The log function is a
  genuine tsum construction in the spectral topology; it is defined for all x,
  although its original documented small domain is ℓ² O. The present node states
  its further convergence on all permitted deep ideals. The smaller small-unit
  set is not used to restrict those ideals.
- The available proof dependency `lem-weil-power-series-exp-hom` is imported
  without `public`: `Sheaf.RingTheory.PowerSeries.ExpSubstHom`,
  `PowerSeries.exp_subst_hom`, whose complete source was read. The coefficient
  DVR theorem is already publicly imported through the required coefficient module.
  The other three log/exp analytic/formal proof nodes currently have no Lean record,
  so there is no module to import for them. The valued-DVR finite-quotient Mathlib
  leaf is a proof input; its infrastructure is not needed for elaborating this signature.

Edge cases checked before writing: ℓ=2 retains the strict bound, so for the unramified
case e=1 the first allowed depth is r=2; r=1 is excluded, as required by its torsion.
For ℓ=3,e=1, r=1 is allowed. A ramified example ℓ=3,e=2 requires r≥2 and excludes
the equality boundary r=1. Zero and negative integer depths cannot satisfy `_hr`.
The zero argument of either series gives log(1)=0 and exp(0)=1; the exponential
contains its constant term. The field cannot be a zero ring. The natural N represents
all positive integer exponents. The ideal carrier contains zero, and no nonempty
or cardinality assumption was added. All universes and variables are explicitly bound.

Searches for an existing statement or construction:

- `msearch.py ... leanfinder`, query "logarithm and exponential give inverse continuous
  homomorphisms on deep principal units of a finite extension of the p-adic numbers":
  eight results including `PadicInt.continuousAddCharEquiv...`, number-field logarithmic
  embeddings, and `Padic.coe_withValRingEquiv_symm`; no matching deep-unit theorem.
- `msearch.py ... loogle`, query `Padic.exp, Padic.log, NormedSpace.exp`: zero hits,
  unknown identifier `Padic.exp`.
- `msearch.py ... leansearch`, query "p-adic exponential logarithm inverse on a deep ideal":
  eight results including `PadicInt.inv`, `NormedSpace.invertibleExp`, p-adic valuation
  and additive-character lemmas; none identifies the specified principal-unit domain,
  strict depth bound, inverse logarithm, and finite-unit exponent.
- `msearch.py ... grep`, regex `principal.?[Uu]nit|logSeries|expSeries|log_exp|exp_log`
  in Mathlib Analysis: 25 hits, principally real/complex exp-log and generic normed
  exponential; no matching p-adic logarithm/exponential result.
- `rg` in the upstream `WeilConjectures` tree and this project's `lean/Sheaf` for
  `principalUnit|principal_unit|DeepPrincipal|deep_principal|adicLog|padicLog|logSeries|logarithm`
  found upstream `NumberTheory/Padics/Logarithm.lean` and the landed coefficient-small-log
  module. I read the upstream definitions and relevant full signatures: its theorem is
  only an injective logarithm homomorphism on ℓ² O, requires an algebraic-closure embedding,
  and supplies neither arbitrary depths nor inverse exponential. It is not an exact match.
- The required upstream item-id search found no `lem-wf-deep-principal-unit-log` declaration.
  The upstream-name index and Mathlib, upstream and project trees have no
  `deepPrincipalUnit_log_exp`, `deepPrincipalUnit` or `deep_principal_unit` declaration.
- Searched the coefficient and DVR sources for normalized valuations and Mathlib's
  discrete-valuation interfaces. The decomposition supplied by the recorded uniformizer
  already expresses the required normalized e, so no new definition is necessary.

There is no statement dispute, correction, new node, or dependency-module repair.
The theorem docstring retains the five-step proof plan, including the repaired
summability justification for substitution and the exponential product evaluation.

## Second reading by NV

No independent second worker was started, as the dispatcher brief forbids starting agents.
The worker delivers directly; the maintainer's independent review is the independent reading.
The clause-by-clause self-check above was made with the node and final module open.
