## Worker report

The module `Sheaf.RingTheory.TateSeparableLocalCotangentCoordinates` states
`RestrictedSeries.tate_separable_local_cotangent_coordinates`. Its only theorem has
proof `sorry`; no definition, instance, axiom, or additional postponed theorem is introduced.
The node statement and proof are unchanged. The only changes to the node are its Lean
record and the addition of the already landed `def-trf-restricted-series-presentation`
to `stmt_deps`, to cite the constants map actually used in the statement.

Hypothesis and clause correspondence (T denotes the written-out restricted-series subring,
R denotes `Localization.AtPrime n`, and κ denotes `T ⧸ n` in this report only):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Arbitrary field with a specified real-valued nonarchimedean absolute value | `F : Type u`, `[NormedField F]`, `[IsUltrametricDist F]`; the absolute value is the specified norm. |
| Completeness and nontrivial absolute value | `[CompleteSpace F]` and `hF : ∃ a : F, a ≠ 0 ∧ ‖a‖ ≠ 1`. This is nontriviality of the absolute value, not just nontriviality of the field. |
| Any nonnegative number r of variables | `r : ℕ`, with variables `Fin r`; no positivity restriction. |
| The actual restricted-series ring T with coefficientwise addition and Cauchy multiplication | `↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ)))`. Its cofinite coefficient decay at radius one is exactly finiteness of coefficients of norm at least each ε > 0. The operations are inherited from `MvPowerSeries`. |
| A proper maximal ideal n and κ = T/n | `n : Ideal T`, `[n.IsMaximal]`, and the actual `Ideal.Quotient` type `T ⧸ n`. Maximality includes properness. |
| κ finite dimensional over F | `hfinite : @Module.Finite F (T ⧸ n) ...`; over a field this is exactly `FiniteDimensional`. The scalar module is explicitly the algebra of `(Ideal.Quotient.mk n).comp (constants F r)`. |
| κ/F separable, with the intended scalar inclusion | `hseparable : @Algebra.IsSeparable F (T ⧸ n) ...` with the same explicit constants-then-quotient algebra. Mathlib defines this as separability of every minimal polynomial. No perfection of F is assumed. |
| R = T localized at n | The actual `Localization.AtPrime n`, with its published local-ring instance. |
| R regular, Noetherian, and local | `IsRegularLocalRing (Localization.AtPrime n)`, a class extending both `IsLocalRing` and `IsNoetherianRing`. |
| p = nR is the maximal ideal | `n.map (algebraMap T R) = IsLocalRing.maximalIdeal R`. All cotangent terms thereafter use this actual maximal ideal. |
| Termwise partial derivatives of restricted series | `∃ d : Fin r → T → T` with `(d i h).val = MvPowerSeries.pderiv F i h.val` for every i and h. The equality specifies the entire series, not just some derivative-like function. Mathlib's coefficient formula is `coeff ν (pderiv F i h) = coeff (ν + single i 1) h * (ν i + 1)`. |
| Residue map rho(h/u) = bar(h)/bar(u), onto κ, kernel p | `∃ ρ : R →+* (T ⧸ n)`, `Function.Surjective ρ`, `RingHom.ker ρ = maximalIdeal R`, and the fraction formula for every `h : T` and `v : n.primeCompl`. Division uses the explicitly written canonical `Ideal.Quotient.field n`, without a file-local instance. The universal fraction equation determines ρ uniquely. |
| Well-defined isomorphism p/p² → κ^r | `θ : IsLocalRing.CotangentSpace R ≃+ (Fin r → T ⧸ n)`. Mathlib's cotangent space is the actual quotient of the maximal ideal by its square; the finite product is the finite direct sum. An additive equivalence already supplies both inverses and well-definedness on quotient classes. |
| κ-linearity for the scalar structure induced by R/p = κ | For every `a : R`, quotient class z and coordinate i, `θ (a • z) i = ρ a * θ z i`. Together with surjectivity and kernel p of ρ, this is exactly κ-linearity: every κ-scalar lifts to a; two lifts differ by p, which annihilates p/p². Conversely any κ-linear equivalence satisfies the displayed equation. Thus this encoding neither chooses an unrelated scalar structure nor loses linearity. It avoids installing a second global module instance on the existing cotangent type. |
| The specified formula [h/u] ↦ (bar(partial_i h)/bar(u)) | For `h : n`, `v : n.primeCompl`, and any maximal-ideal element z whose value equals `IsLocalization.mk' R h.val v`, the coordinate of `θ (maximalIdeal.toCotangent z)` is exactly that quotient using `d i h.val`. Quantifying z with its equality avoids inserting an auxiliary membership proof/theorem. Every such fraction is in p, and every element of p has such a representative. |
| r = 0 gives T = R = κ = F, n = p = 0, and zero spaces | The final `r = 0 → ...` states both ideal equalities, three ring equivalences `eT`, `eR`, `eκ` normalized to send the corresponding constants to a, and `Subsingleton` for both vector-space types. Canonical ring equivalences render the paper's identifications between different quotient/localization types; no literal equality of types or additional coefficient field is assumed. |

Dependency declarations read and used:

- `def-weil-pbc-localization-at-prime`: the recorded
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`, including
  the fraction model and local-ring instance. The other recorded clauses were read in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` (`Ideal.ResidueField`) and
  `Mathlib.RingTheory.LocalRing.ResidueField.Fiber` (`Ideal.Fiber`). The item itself
  uses T/n as specified, rather than silently replacing it by a different residue type.
- `def-weil-regular-scheme`: its unchanged ring clauses are the recorded
  `mathlib_match`, `IsRegularLocalRing` and `IsRegularRing` in
  `Mathlib.RingTheory.RegularLocalRing.Defs`. The newer Lean record
  `AlgebraicGeometry.IsRegularScheme` in `Sheaf.AlgebraicGeometry.IsRegularScheme`
  was also opened: it is the locally Noetherian/stalkwise scheme clause and is not
  needed for this ring statement. The module imports the exact ring clause it uses.
- Added existing statement dependency `def-trf-restricted-series-presentation`:
  `Sheaf.RingTheory.RestrictedSeriesPresentation`, `RestrictedSeries.constants`.
  This is the existing canonical scalar map, not a private copy.
- Proof-only imports follow all stated proof dependencies:
  `RestrictedSeries.affinoid_polynomial_closed_point_comparison`
  (`Sheaf.RingTheory.AffinoidPolynomialClosedPointComparison`);
  `IsLocalization.isNoetherianRing` (`Mathlib.RingTheory.Localization.Submodule`);
  `MvPolynomial.isRegularRing_of_isRegularRing`
  (`Mathlib.RingTheory.RegularLocalRing.Polynomial`);
  `MvPolynomial.ringKrullDim_localizationAtMaximal`
  (`WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension`);
  `AdicCompletion.isRegularLocalRing_iff`
  (`WeilConjectures.RingTheory.CompletionRegularLocal`);
  `RingTheory.completion_dimension` (`WeilConjectures.RingTheory.CompletionDimension`).
  The cotangent-dimension proof dependency is already in the public ring-definitions
  import: `IsRegularLocalRing.iff_finrank_cotangentSpace` and its imported cotangent API.
  These proof sources and their full signatures/docstrings were read; only the
  recorded proof plan is supplied here.

Edge cases checked before writing: r = 0 is present explicitly, including the three
canonical identifications and both zero spaces. Maximality excludes the unit ideal
and the zero residue ring, so all denominators outside n have nonzero residue.
A zero numerator and different fraction representatives are covered by the universal
formula on a quotient class. Non-rational separable closed points are allowed: κ
is T/n and is never replaced by F; no choice of a coefficient field in R is made.
Positive characteristic is allowed, including vanishing integer derivative coefficients;
separability is imposed only on the specified finite residue extension, not on F.
The universe u is explicit; the quotient and localization stay in that universe,
and all variables and structure arguments are explicitly bound.

Searches made with the prescribed msearch.py (group ND, this item):

- LeanFinder: “The cotangent space of a Tate algebra at a finite separable residue field
  is isomorphic to the coordinate vector space by partial derivatives”: 8 hits,
  headed by `Algebra.SubmersivePresentation.cotangentEquiv` and its application lemma;
  these concern algebraic submersive presentations, not this Tate local ring.
- Loogle: `"Cotangent", "map"`: 12 hits including `Ideal.mapCotangent`,
  `Ideal.map_toCotangent_ker`, and `Ideal.Cotangent.lift`; none states this node.
- LeanSearch: “Tate algebra separable closed point cotangent coordinates”: 8 hits,
  including general `IsLocalRing.CotangentSpace` and algebraic extension cotangent
  objects, with no Tate derivative comparison.
- Mathlib grep: `TateAlgebra|RestrictedPowerSeries|separable.*cotangent`: 0 hits.
  Direct source inspection additionally found the exact restricted subring in
  `Mathlib/RingTheory/MvPowerSeries/Restricted.lean`, the exact formal derivative in
  `MvPowerSeries/Derivative.lean`, and the quotient cotangent in `Ideal/Cotangent.lean`.
- Project rg: `tate_separable_local_cotangent|TateAlgebra|IsRestricted.subring` in
  `lean/WeilConjectures/RingTheory` and `lean/Sheaf/RingTheory`: only the existing
  restricted-series presentation, Grauert--Remmert, and affinoid/polynomial comparison
  modules, no theorem of this node. Broader project searches for RestrictedSeries,
  TateAlgebra and restricted derivatives likewise found no matching statement.
  The exact item-id search by `grep -rn` in `lean/WeilConjectures` had no hits.

Sources opened: the node and every statement dependency, all recorded declarations,
Mathlib's quotient field, cotangent, restricted-series and derivative definitions;
Conrad's https://math.stanford.edu/~conrad/papers/aws.pdf, Theorem 1.1.5(1), PDF p.4,
and https://www.numdam.org/article/AIF_1999__49_2_473_0.pdf, including the cited
regularity/derivation discussion. The first source explicitly gives regularity and
local dimension; the separable cotangent refinement is the node's recorded agent
argument, reproduced step by step in the theorem docstring.

No statement dispute, statement correction, new node, or dependency-interface repair.
All compilations use the prescribed server scompile.py; validation results follow below.

## Second reading by ND

Written by the maintainer's independent reviewer (stage-2 review of 00e0a542), replacing the
earlier placeholder, which only said that no second worker reading was made.

Node clauses and their Lean rendering, each read against the Mathlib/project declarations:

1. F a field complete for a nontrivial real-valued nonarchimedean absolute value:
   `[NormedField F] [IsUltrametricDist F] [CompleteSpace F]` and `hF : ∃ a ≠ 0, ‖a‖ ≠ 1`.
   NormedField norms are multiplicative, so this is an absolute value. hF is exactly
   nontriviality. Correct, and nothing stronger is assumed.
2. r ≥ 0 and T = F⟨x_1..x_r⟩: `MvPowerSeries.IsRestricted.subring (fun _ : Fin r ↦ 1)`. At
   radius 1, `IsRestricted` (Restricted.lean:33) is `‖coeff t f‖ * 1 → 0` along cofinite, which
   is the node's "finitely many |a_ν| ≥ ε". The ring operations are MvPowerSeries
   coefficientwise addition and Cauchy multiplication. Correct.
3. A maximal ideal n with κ = T/n: `n : Ideal T`, `[n.IsMaximal]`, the actual `T ⧸ n`. Correct.
4. κ/F is finite and separable. The algebra map is `(Ideal.Quotient.mk n).comp (constants F r)`.
   Here `RestrictedSeries.constants` is the landed codRestrict of `MvPowerSeries.C`
   (def-trf-restricted-series-presentation). The explicit `@` is needed because a Subring
   carries no F-algebra instance. `Module.Finite` matches the node's finite-dimensional
   condition, and `Algebra.IsSeparable` (every minpoly separable) matches its distinct-roots
   condition. Correct.
5. R = T_n: `Localization.AtPrime n`, the recorded Mathlib owner of
   def-weil-pbc-localization-at-prime. p = nR: the clause `n.map algebraMap = maximalIdeal R`.
   Correct.
6. R is a regular Noetherian local ring: `IsRegularLocalRing R` (mathlib_match ring clause of
   def-weil-regular-scheme, which extends IsLocalRing and IsNoetherianRing). Correct.
7. Termwise derivatives: `∃ d`, with `(d i h).val = MvPowerSeries.pderiv F i h.val` for all
   i and h. This pins d completely and also asserts that restrictedness is preserved, which
   is true in the ultrametric case. Not arbitrary.
8. ρ(h/u) = h̄/ū: `∃ ρ : R →+* T ⧸ n`, surjective, kernel maximalIdeal R, and the formula on
   every `mk' h v`. Division uses `Ideal.Quotient.field n`. The formula determines ρ.
9. θ : p/p² ≃ κ^r is κ-linear. In Lean, θ is a `CotangentSpace R ≃+ (Fin r → T ⧸ n)` with
   `θ (a • z) i = ρ a * θ z i`. Since ρ is surjective with kernel p, this is exactly
   κ-linearity for the R/p = κ scalar structure.
10. The formula [h/u] ↦ (∂_i h mod n)/ū for h ∈ n: the Lean quantifies over every z ∈ p with
    z = mk' h v. Every element of p has such a representative, and toCotangent is surjective,
    so θ is completely pinned.
11. The r = 0 clause: n = ⊥, maximalIdeal = ⊥, ring isomorphisms eT, eR and eκ normalized on
    constants (which determines them, because constants is onto when r = 0), and both spaces
    Subsingleton. Correct.

Edge cases checked: r = 0 (above), imperfect F and positive characteristic (separability is
imposed only on κ/F), non-rational closed points (κ ≠ F is allowed). The universe is a single
u, and every variable is bound.

One definition per notion: there is no project derivative on restricted series. The only
IsRestricted users in lean/Sheaf are GrauertRemmert, NonarchimedeanSeriesSubstitution,
AffinoidPolynomialClosedPointComparison and RestrictedSeriesPresentation, and none states
this result. The consumer lem-per-separable-regular-affinoid-residual-conormal has no Lean
record yet.

Records: the item record changes only `lean` and adds the landed stmt_dep
def-trf-restricted-series-presentation, whose `constants` the statement uses. The
lean.statement equals the file signature verbatim, and no line exceeds 99 characters.

Docstrings: the module and the theorem both give the source place and the blueprint id. The
theorem docstring follows proof steps 1–6. The proof is `sorry`, with no definitions,
instances or axioms. Plain imports are the proof-dependency modules.

Mismatches: none in the Lean. This section was the only change.

Worker validation, kept from the replaced section: `deliver2.py ND
lem-per-tate-separable-local-cotangent-coordinates --no-push` returned OK (dry run, commit
98ba9c4aad8), and the module compiled cleanly in sandbox and library forms on the server.
