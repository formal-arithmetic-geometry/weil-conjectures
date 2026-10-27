## Worker report

The module `Sheaf.RingTheory.NormalFinitePrimaryDichotomy` states the two cases of
`lem-per-normal-finite-primary-dichotomy` as two named theorems, each with its whole
proof `sorry`. No definition, axiom, additional assumption, or statement correction
is introduced. Every other node field is preserved. Both the sandbox module and
the final library module compiled cleanly through the prescribed `scompile.py`.

The source was read directly with `pdftotext -f 71 -l 73 -layout` on
`literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`:
printed p.65 V 2.2.3 distinguishes ideals admitting a nonzero base equation;
printed p.67 V 3.2.3(i),(ii) distinguishes a height-one symbolic power from an
ideal whose image has a base equation nonzero modulo the coefficient maximal ideal.
The node uses the equivalent contraction formulation, and its six proof steps
are retained in the DVR theorem docstring. The field theorem's docstring gives
exactly the first proof step that proves that case.

Hypothesis and conclusion correspondence:

- Coefficient field: `(Λ : Type u) [Field Λ]` in
  `MvPowerSeries.exists_nonzero_mem_primary_of_finite_normal_field`.
- Complete discrete valuation coefficient ring: `(Λ : Type u) [CommRing Λ]
  [IsDomain Λ] [IsDiscreteValuationRing Λ]` and
  `[IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ]` in
  `MvPowerSeries.primary_dichotomy_of_finite_normal_complete_dvr`.
  Completeness is completeness and separatedness for the maximal-ideal adic
  topology; no separate or arbitrary topological structure is imposed.
- Positive number of variables: `(r : ℕ) (hr : 1 ≤ r)` in both statements.
- The specified ring `R`: `MvPowerSeries (Fin r) Λ` throughout. `Fin r` indexes
  precisely the named finite family of variables; the coefficient inclusion is
  `MvPowerSeries.C`.
- The finite inclusion `R ↪ A`: `[Algebra (MvPowerSeries (Fin r) Λ) A]`,
  `[Module.Finite (MvPowerSeries (Fin r) Λ) A]`, and
  `hinj : Function.Injective (algebraMap (MvPowerSeries (Fin r) Λ) A)`.
  An algebra over `R` is exactly the given unital commutative-ring map and its
  induced module structure. There is no independently chosen Λ-algebra structure
  requiring an extra compatibility assumption.
- A Noetherian normal domain: `(A : Type v) [CommRing A] [IsDomain A]
  [IsNoetherianRing A] [IsIntegrallyClosed A]` in both statements.
- Nonzero proper primary ideal: `(Q : Ideal A) (hQ0 : Q ≠ ⊥)
  (hQ : Q.IsPrimary)`. Read `Ideal.isPrimary_iff`: it includes `Q ≠ ⊤`, and
  `xy ∈ Q` implies `x ∈ Q ∨ y ∈ Q.radical`, exactly the required primaryness.
  For a proper ideal an exponent witnessing membership in its radical cannot
  be zero, because that would put 1 in Q. Thus Mathlib's natural exponents
  express the node's exponents at least one without a change in meaning.
- Field conclusion: `∃ g : MvPowerSeries (Fin r) Λ, g ≠ 0 ∧
  algebraMap (MvPowerSeries (Fin r) Λ) A g ∈ Q` expresses exactly a nonzero
  element of the contraction `Q ∩ R`.
- Chosen uniformizer: `(π : Λ) (hπ : IsLocalRing.maximalIdeal Λ = Ideal.span {π})`.
  The DVR class ensures its maximal ideal is nonzero, so this already implies
  `π ≠ 0`; no extra hypothesis is necessary.
- First DVR alternative: an existential `g` with its image in Q and
  `MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {π})) g ≠ 0`.
  Read the full definition of `MvPowerSeries.map`: it applies the coefficient
  ring homomorphism to each coefficient. Its target here is exactly
  `MvPowerSeries (Fin r) (Λ ⧸ Ideal.span {π})`.
- Second DVR alternative: `∃ P : PrimeSpectrum A` gives a prime ideal with
  `P.asIdeal = Q.radical`. This is the prescribed radical, not an arbitrary
  unrelated height-one prime. Mathlib `Ideal.radical` is the ideal of elements
  whose some natural power belongs to Q, again with zero exponent excluded
  automatically by properness.
- Height one: `P.asIdeal ≠ ⊥` and
  `∀ T : Ideal A, T.IsPrime → ⊥ < T → T < P.asIdeal → False`.
  This writes the node's explicit prime-chain definition literally. The
  existential `PrimeSpectrum` supplies primality without any assumed primality
  of Q or any assumption that its radical has height one.
- Contains π: `algebraMap (MvPowerSeries (Fin r) Λ) A (MvPowerSeries.C π)
  ∈ P.asIdeal`, using precisely the composite coefficient inclusion.
- Positive symbolic exponent: `∃ n : ℕ, 1 ≤ n ∧ ...`.
- Symbolic power equality: the equality to
  `Ideal.comap (algebraMap A (Localization.AtPrime P.asIdeal))
    (Ideal.map (algebraMap A (Localization.AtPrime P.asIdeal)) (P.asIdeal ^ n))`
  is exactly `Q = {a | a/1 ∈ P^n A_P}`. `Ideal.map` extends the ordinary ideal
  power, `Ideal.comap` contracts it. There is no alternative notion of symbolic
  power and no arbitrary localization map.
- The two coefficient cases use independent explicitly declared universes `u v`;
  neither the algebra universe nor the coefficient characteristic is restricted.

Dependency declarations read and used:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing` and
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`, `MvPowerSeries.C`,
  `MvPowerSeries.map`, `Mathlib.RingTheory.MvPowerSeries.Basic`.
- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`.
- `def-weil-pbc-normal-ring`: `IsIntegrallyClosed`, together with `IsDomain`,
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`. This uses exactly the
  recorded normal-domain branch, rather than a private normal-ring predicate.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`. The residue-field and fibre
  clauses of that dependency are not used by this node.

All statement dependency modules are public imports. The modules of recorded
proof dependencies are imported without `public`: finite-integrality,
incomparability, power-series domain and Noetherianity, principal-ideal height,
Noetherian localization and localization height are the corresponding Mathlib
modules. Normal localization and DVR uniformizer factorization are already
available in the public statement imports. The upstream recorded module
`WeilConjectures.AlgebraicGeometry.Regular` is a proof import for
`lem-sc-normal-dim1-dvr`; this delivery does not replace or repair that record.

Edge cases checked mathematically before writing:

- `r = 1` is included; `r = 0` is excluded exactly as the node requires.
- The zero ring for either domain, Q = 0, and Q = A are excluded precisely by
  the domain, nonzero, and primary hypotheses. No additional nontriviality or
  nonvanishing assumption is inserted.
- In the identity finite algebra over a field, Q = (t₁) gives the field conclusion.
- Over a complete DVR, Q = (t₁) gives a base series with nonzero reduction.
- Q = (π²) gives the second alternative, with radical (π) and n = 2.
- Q = (π,t₁)² has radical of height two, so it must give the first alternative;
  t₁² belongs to Q and has nonzero reduction.
- Ramification, for example adjoining a root s of π, does not require π itself
  to generate the radical in A_P: the conclusion permits its own uniformizer
  and arbitrary positive symbolic exponent (e.g. Q = (s³)).
- Exponent zero cannot satisfy properness, so n ≥ 1 is essential and is retained.
- The node asserts a disjunction, and the Lean uses `∨` without adding uniqueness
  or exclusivity of the alternatives.

Searches for an existing statement:

1. `msearch.py Q64 lem-per-normal-finite-primary-dichotomy leanfinder` with
   query "A primary ideal in a normal finite algebra over multivariate power
   series over a discrete valuation ring either contains a series nonzero
   modulo the uniformizer or is a symbolic power of a height one prime".
   Eight hits: DVR ideal powers, uniformizer powers, and separate power-series
   prime-ideal results; none states this dichotomy.
2. `msearch.py ... loogle '"IsPrimary", "IsIntegrallyClosed"'`: zero hits.
3. `msearch.py ... grep
   'symbolic[Pp]ow|symbolic_pow|IsPrimary.*[Hh]eight|[Hh]eight.*IsPrimary'`:
   zero hits.
4. `msearch.py ... leansearch` with query "Primary ideals in a finite normal
   domain over a power series ring over a discrete valuation ring either have
   contraction not contained in the uniformizer ideal or are symbolic powers
   of height one primes": eight hits, including `Ideal.IsPrimary`,
   `Ideal.isPrimary_iff`, `Ideal.isPrime_radical`, and DVR ideal powers;
   no full dichotomy. These hits confirmed the existing primary-ideal interface.
5. `rg -n` over `lean/WeilConjectures` and `lean/Sheaf` with
   `symbolic[Pp]ow|symbolic_pow|primary.*dichotomy|normal_finite_primary|IsPrimary.*[Hh]eight|[Hh]eight.*IsPrimary`:
   no matches. `grep -rn 'lem-per-normal-finite-primary-dichotomy'
   lean/WeilConjectures`: no matches. A separate exact-name search for
   `normal_finite_primary|normalFinitePrimary` in Mathlib, WeilConjectures and
   Sheaf also found no matches. Source reads of primary ideals, radical,
   coefficient maps, completeness, prime spectra, and each dependency signature
   confirmed the definitions above.

No disputed statement or node fault was found. No new node or dependency module
was needed. Compilation used only the authorized server wrapper and succeeded
for both compilation modes; no warning was reported.

## Second reading by Q64

No second reading by another worker: the dispatcher prohibits starting agents,
and the maintainer's independent review reads the delivery. I reread the node
and the completed signatures clause by clause using the correspondence above.
The checks focused on retaining the field case, the completeness assumption,
properness through `IsPrimary`, the specified radical, the strict-chain height
condition, coefficientwise reduction, and a positive symbolic power through
prime localization. No mismatch requiring a change was found.
