## Worker report

The module `Sheaf.RingTheory.EppPerfectCoreCompleteLocal` states
`IsLocalRing.epp_perfect_core_complete_local`, with its entire proof `sorry`.
It introduces no definitions and changes only the item's `lean` record. The
previously removed module has no surviving declaration in the read library;
this delivery states the node again against the current live library.

Source read directly from the supplied ILO PDF: printed pages 55–56, Exposé IV
3.2.1–3.2.3, and printed page 58, 4.2.3. The latter explicitly applies (i) and
(iv) to the complete local domains A/p. Since k₀ is perfect, algebraicity over
k₀ is equivalent to the separable algebraicity used in the source's Epp property.
The module docstring reproduces all seven steps of the node's proof, including
the automatic compatibility of coefficient representatives with the specified k₀.

Hypothesis and clause correspondence:

- Prime p: `(p : ℕ) [Fact p.Prime]`.
- Perfect field k₀ of characteristic p:
  `(k₀ : Type u) [Field k₀] [CharP k₀ p] [PerfectRing k₀ p]`.
  `PerfectRing` says that the p-th power map is bijective. In a field of prime
  characteristic that map is injective, so this is exactly the stated surjectivity.
- A complete Noetherian local integral domain R of characteristic p:
  `(R : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]`
  and `[CharP R p] [IsAdicComplete (maximalIdeal R) R]`.
  `IsLocalRing` on commutative rings means a unique maximal ideal; `IsDomain`
  includes nontriviality and cancellation, equivalently no zero divisors.
  Completeness includes separatedness, and is equivalent to bijectivity of the
  canonical map to the adic completion, rather than only Cauchy completeness.
- The specified inclusion k₀ → R: `[Algebra k₀ R]`. Its unital ring map is
  injective because k₀ is a field and R is nontrivial. No arbitrary map or
  additional coefficient-field choice occurs in the signature.
- k = R/m: `IsLocalRing.ResidueField R`, whose definition is exactly that quotient.
  Its k₀-algebra structure is induced from the given k₀ → R and the quotient map.
- F = Frac(R): `FractionRing R`, the localization at the nonzero divisors.
  Since R is a domain this is its fraction field. Its k₀-algebra structure is
  the one induced through R and its canonical localization map.
- The perfect core of either field E: `(∀ n : ℕ, ∃ y : E, y ^ (p ^ n) = x)`.
  This says exactly that x lies in every set E^(p^n); there is no independent
  notion or private replacement for a dependency declaration here.
- Residue-field hypothesis: `hres : ∀ x : ResidueField R, ... → IsAlgebraic k₀ x`.
  The omitted expression here is precisely the all-n root condition above.
- Conclusion: `∀ x : FractionRing R, ... → IsAlgebraic k₀ x`, with the same
  root condition. `IsAlgebraic k₀ x` is defined as the existence of a nonzero
  polynomial over k₀ whose evaluation at x is zero, exactly the node's last clause.

Dependency declarations read and used:

- `def-weil-field`: Mathlib's `Field`,
  `Mathlib.Algebra.Field.Defs`, read with its full class signature and docstring.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` from
  `Mathlib.RingTheory.Noetherian.Defs`, an abbreviation for `IsNoetherian R R`.
  The adjacent `isNoetherianRing_iff_ideal_fg` confirms the ideal formulation.
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete` from
  `Mathlib.RingTheory.AdicCompletion.Basic`, read together with `IsHausdorff`,
  `IsPrecomplete`, and `AdicCompletion.of_bijective_iff`.
- Supporting Mathlib declarations: `PerfectRing` from `Mathlib.FieldTheory.Perfect`,
  `IsAlgebraic` from `Mathlib.RingTheory.Algebraic.Defs`, `ResidueField`, `residue`,
  and `ResidueField.algebra` from `Mathlib.RingTheory.LocalRing.ResidueField.Basic`
  (the field definition itself is in its imported `Defs`), and `FractionRing`
  from `Mathlib.RingTheory.Localization.FractionRing`.

Proof-only imports follow the node's recorded plan:
`WeilConjectures.RingTheory.CompleteLocalDomainFiniteOverRegular`
(`IsLocalRing.complete_local_domain_finite_over_regular`, whose full signature
and proof docstring were read), `Mathlib.RingTheory.MvPowerSeries.Basic`
(`MvPowerSeries`), and `Mathlib.RingTheory.LaurentSeries` (`LaurentSeries` and
its Hahn-series interface). `lem-per-finite-extension-perfect-core` currently
has no Lean record or Mathlib match, so it contributes no import. It is used
only in the natural-language proof plan and is not needed to type this statement.
There are no new nodes, dependency modules, or statement corrections.

Edge cases checked:

- n = 0 imposes only existence of a first-power root, supplied by x itself;
  the quantifier includes every higher n as required.
- x = 0 is included in both quantifiers and is algebraic by the polynomial T.
- If R is a field, its maximal ideal is zero and the statement includes that
  case; there is no positive-dimension or nonzero-maximal-ideal assumption.
- The prime 2 is included; characteristics 0 and 1 are excluded by the node's
  prime-characteristic assumption, not an extra restriction.
- k₀ and R have independent universes u and v. There is no finite generation,
  residue algebraicity outside the perfect core, or separability assumption on
  the Cohen fraction-field extension.
- The algebra structure is the specified inclusion, so the hypothesis and
  conclusion refer to the same k₀, rather than an unrelated coefficient field.

Searches for an existing declaration, on 2026-10-24:

- `msearch.py ... leanfinder`, query: “The perfect core of the fraction field of
  a complete Noetherian local domain is algebraic over a perfect subfield if
  the residue field perfect core is algebraic over it”. Eight hits, including
  `perfectClosure.isAlgebraic`, algebraicity of residue extensions,
  `Algebra.IsAlgebraic.perfectField`, `perfectClosure.perfectField`, formal
  smoothness over perfect fields, and `IsLocalRing.ResidueField.algebra`.
  None asserts this complete-local fraction-field theorem. In particular the
  relative perfect closure is a different notion from intersection of Frobenius images.
- `msearch.py ... loogle 'PerfectField, FractionRing'`: one hit,
  `Ring.HasFiniteQuotients.instPerfectFieldResidueFieldOfFractionRing`; it assumes
  the whole fraction field perfect and proves residue-field perfectness, not this lemma.
- `msearch.py ... grep 'perfectCore|perfect_core|Epp|epp_perfect'`: 25 unrelated
  text hits, largely tactic identifiers and “stepping stone”; no relevant declaration.
- More focused `msearch.py ... grep
  'perfectCore|perfect_core|[Mm]aximal.*perfect|[Pp]erfect.*[Ss]ubfield' FieldTheory`:
  one comment in `PurelyInseparable/PerfectClosure.lean` about maximal purely
  inseparable subextensions; no perfect-core complete-local theorem.
- `rg` for `perfectCore|perfect_core|epp_perfect|lem-per-epp-perfect-core-complete-local`
  in both `lean/WeilConjectures` and `lean/Sheaf`: only unrelated perfect-complex
  core theorems. `grep -rn` for this item's id in `lean/WeilConjectures`: no hits.
  A further `rg` for the theorem name and Epp/complete-local patterns in
  `dag/lean_names_upstream.json`, `lean/Sheaf`, and `lean/WeilConjectures` found no match.

Validation: the required `scompile.py N7 lem-per-epp-perfect-core-complete-local`
compiled this module on the server in both sandbox and library-path modes,
each in 1.3 seconds, exit 0, with no errors or unexpected warnings. All Lean
lines have at most 100 characters. Every variable and universe is explicit.

## Second reading by N7

This is a second pass by the same worker, not an independent-agent review;
the dispatcher explicitly prohibits starting other agents. I reopened the node
and read the completed signature against it. The three field assumptions on k₀
match field, characteristic p, and perfectness. The six ring conditions on R
match the stated commutative, local, Noetherian, integral-domain,
characteristic-p, and maximal-ideal-complete hypotheses. `Algebra k₀ R`
supplies the specified inclusion. The root quantifiers in `hres` and the
conclusion have identical n ranges and exponents, differing only in the
prescribed residue and fraction fields, and both conclusions use `IsAlgebraic k₀`.
There is no extra finite-dimensionality assumption or restriction to nonzero x.
No mismatch or statement correction was found. The seven-step docstring retains
the coefficient-field compatibility argument and the inseparable finite-extension
case. The node copy preserves all original fields except `lean`.
