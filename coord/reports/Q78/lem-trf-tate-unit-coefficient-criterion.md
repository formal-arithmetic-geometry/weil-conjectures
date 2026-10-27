## Worker report

The module `Sheaf.RingTheory.TateUnitCoefficientCriterion` states
`RestrictedSeries.tate_unit_coefficient_criterion`, with `sorry` as its whole proof.
No definition, dependency interface, or natural-language node statement changes.

Source checked directly: [Bosch, Lectures on Formal and Rigid Geometry (2008)](https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf),
Section 1.2, Corollary 4, printed p.10, PDF page index 11. The arbitrary-series
clause is the strict inequality between the tail Gauss norm and the constant norm;
the proof normalizes the norm, reduces to a nonzero constant, and uses a geometric
series. The declaration docstring gives all four steps of the DAG proof, including
norm attainment and the zero-variable case, with the dependency ids.

Hypothesis and clause correspondence:

- The complete field with nontrivial, real-valued, multiplicative absolute value
  is `(K : Type u) [NontriviallyNormedField K] [CompleteSpace K]`. `NormedField`
  extends `Field`, has real-valued norm, and requires multiplicativity; the
  nontriviality field asserts existence of an element of norm greater than one,
  equivalently a nonzero element of norm different from one. The metric is the
  norm metric. `[IsUltrametricDist K]` is the nonarchimedean condition.
- The arbitrary integer r >= 0 is `(r : ℕ)`, including zero, and the r variables
  are indexed by `Fin r`. The universe `u` is explicit and unrestricted.
- The ring T_r is exactly `MvPowerSeries.IsRestricted.subring (R := K)
  (fun _ : Fin r ↦ (1 : ℝ))`, as used by the dependency's constants map. Its
  addition and multiplication are inherited from formal series: coefficientwise
  addition and finite Cauchy multiplication. Restrictedness at radius one is
  cofinite convergence of the coefficient norms to zero, not formal convergence.
- The coefficient c_0 is `MvPowerSeries.constantCoeff f.val`; its embedding back
  into T_r is the recorded `RestrictedSeries.constants K r`.
- The Gauss norm is `MvPowerSeries.gaussNorm (norm : K → ℝ)
  (fun _ : Fin r ↦ 1)`, whose definition is the supremum of the coefficient
  norms times radius monomials. At radius one these factors are all one.
  Restrictedness implies boundedness of this family, so the real supremum is
  finite. The tail is the actual subtraction in T_r, followed by `.val`.
- The main first conjunct is `IsUnit f ↔ gaussNorm ... < ‖constantCoeff f.val‖`.
  `IsUnit` refers to the restricted subring, so its inverse must be restricted.
  For this commutative ring it is equivalent to existence of g with f*g = 1.
- The second conjunct states that this same strict inequality implies
  `MvPowerSeries.constantCoeff f.val ≠ 0`, rendering the stated consequence.
- The last conjunct is guarded by `r = 0`. It says f equals its constant series
  and the tail norm is zero. Thus the constants embedding identifies T_0 with K:
  it is surjective by the first equality and injective by constant coefficient.
  No hypothesis r > 0 is imposed, and the main iff still holds for r = 0.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`; its complete
  signature and docstring were read. It is inherited by `NontriviallyNormedField`.
- `def-trf-restricted-series-presentation`: the full landed module
  `Sheaf.RingTheory.RestrictedSeriesPresentation` was read, in particular
  `RestrictedSeries.constants` and its radius-one subring type. The declaration
  `RestrictedSeries.IsTopologicallyFinitelyPresented` is not a hypothesis of the
  item, so that additional presentation property is not assumed here.
- Mathlib `MvPowerSeries.IsRestricted`, `MvPowerSeries.IsRestricted.subring`, and
  `MvPowerSeries.gaussNorm` were read at their definitions and used directly.
- Recorded proof leaves `MvPolynomial.dvd_C_iff_exists` in
  `Mathlib.Algebra.MvPolynomial.NoZeroDivisors` and
  `isUnit_one_sub_of_norm_lt_one`, `Units.oneSub`, `hasSum_geom_series_inverse`
  in `Mathlib.Analysis.SpecificLimits.Normed` were read and their modules are
  plain proof imports. The other three proof dependencies have no recorded
  declarations in the read snapshot, so there are no modules to import for them.
  They are not needed to type the statement and are named in its proof docstring.

Edge cases checked before writing: f = 0 gives neither a unit nor a strict
inequality; a nonzero constant has zero tail and satisfies the criterion; r = 0
has only the zero multi-index and reduces to nonvanishing in K; for r > 0 the
series 1-X has constant norm one and tail norm one and is not a restricted-series
unit (its formal inverse has infinitely many coefficients of norm one). A tail
whose norm equals the constant norm must be excluded, so the comparison is strict.
No discretely valued, densely valued, algebraically closed, or characteristic-zero
assumption is added. For nondiscrete norms restrictedness still ensures that a
nonzero tail attains its norm, as explained in the docstring.

Searches made through `msearch.py Q78 lem-trf-tate-unit-coefficient-criterion`:

- leanfinder: `A restricted power series over a complete nonarchimedean field is
  a unit if and only if its constant coefficient has norm strictly greater than
  the Gauss norm of the nonconstant tail`. Eight hits, including
  `PowerSeries.isUnit_iff_constantCoeff`, `PowerSeries.isUnit_weierstrassUnit`, and
  `MvPowerSeries.isUnit_iff_constantCoeff`; none gives a restricted inverse.
- loogle: `"IsUnit", "gaussNorm"`. Zero hits.
- grep: `isUnit.*gauss|gauss.*isUnit|TateAlgebra|restricted.*unit`. Thirteen hits:
  Gauss sums, restricted products, and the restricted-series definition; no match.
- leansearch: `A series in a Tate algebra over a complete nonarchimedean field is
  invertible exactly when the norm of its constant coefficient is strictly larger
  than the Gauss norm of the nonconstant tail`. Eight formal-series hits;
  none states the restricted-ring criterion.
- Local `rg` in `lean/WeilConjectures` and `lean/Sheaf` for restricted-series,
  Gauss-norm/unit, and proposed declaration names: only the presentation and
  affinoid results, no duplicate. A search for the item id in
  `lean/WeilConjectures` had no hit. The formal-series criterion in
  `Mathlib/RingTheory/MvPowerSeries/Inverse.lean` was read and ruled out by 1-X.
  Proposed-name search in `dag/lean_names_upstream.json` also had no hit.

No statement dispute or node fault was found. The historical CompactObject sample
is withdrawn; its node points to `WeilConjectures.CategoryTheory.CompactObject`,
which was read for the current module/docstring conventions.

## Second reading by Q78

The section delivered under this heading was the worker re-reading its own work ("This is the
same worker's second pass, not a claim of independent review"). The maintainer's reviewer
replaced it with the independent clause-by-clause reading below (review of a4f74c032c8b,
2026-10-24). The Lean module and the node record are unchanged.

Node clauses, the Lean that renders each, and the verdict:

1. K is a complete field with a nontrivial real-valued multiplicative nonarchimedean absolute value:
   `(K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`.
   `NormedField` is a `Field` (def-weil-field) with a multiplicative real norm. `NontriviallyNormedField`
   adds an element of norm > 1, which is nontriviality. `IsUltrametricDist` is the nonarchimedean condition.
   Completeness is in the norm metric. The universe u is free. Nothing stronger is assumed. Exact.
2. r ≥ 0 and T_r = K⟨X_1..X_r⟩ (def-trf-restricted-series-presentation): `(r : ℕ)` and
   `MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))`. This is the radius-one
   carrier that the dependency's `RestrictedSeries.constants` uses. Mathlib `IsRestricted` at c = 1
   means ‖coeff t f‖ → 0 along the cofinite filter. Ring operations are those of
   `MvPowerSeries`: coefficientwise addition and Cauchy product. Exact.
3. ‖f‖_G = sup_ν |c_ν|: `MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ ↦ 1)`, which is
   ⨆ t, ‖coeff t f‖ · t.prod (1 ^ ·) = ⨆ t, ‖coeff t f‖. A restricted family is bounded, so
   the real iSup is the true supremum and not the junk value 0. Exact.
4. c_0 and f − c_0: `MvPowerSeries.constantCoeff f.val` and `(f - constants K r c₀).val`, a
   subtraction in T_r with the recorded constants map. Exact.
5. f is a unit (∃ g ∈ T_r, fg = 1) ⇔ |c_0| > ‖f − c_0‖_G: `IsUnit f ↔ gaussNorm … < ‖c₀‖`.
   `IsUnit` is taken in the subring, so the inverse is restricted. In a commutative ring it is
   equivalent to ∃ g, f g = 1. The inequality is strict and has the same direction. Exact.
6. "In particular c_0 ≠ 0 in this condition": the second conjunct, strict inequality → c₀ ≠ 0. Exact.
7. r = 0 is included, with T_0 = K and tail norm 0: the main iff has no r > 0 guard. The third
   conjunct (r = 0 → f = constants c₀ ∧ tail Gauss norm = 0) states the identification
   (surjectivity of the constants map; injectivity is via constantCoeff) and the zero tail. Exact.

Source: Bosch, Lectures on Formal and Rigid Geometry (2008), §1.2. Corollary 4 on printed
p.10: f ∈ R⟨ζ⟩ is a unit iff |f(0)| > |c_ν| for all ν ≠ 0. This equals the node's strict sup
form, because a nonzero restricted tail attains its supremum (proof step 1, in the docstring).

Edge cases: f = 0 satisfies neither side (0 < 0 fails). Nonzero constants have tail 0 and are
units. 1 − X (r ≥ 1) has tail norm 1 = |c₀| and is no restricted unit, which shows why the inequality
is strict. For r = 0, Fin 0 →₀ ℕ is a single point. Value groups that are not discrete need no extra
assumption.

One definition per notion: no IsUnit lemma in Mathlib's MvPowerSeries/Restricted.lean,
GaussNorm.lean or PowerSeries/Restricted.lean. The project Sheaf files that use `IsRestricted`
(GrauertRemmertPowerbounded, AffinoidPolynomialClosedPointComparison,
NonarchimedeanSeriesSubstitution, RestrictedSeriesJacobian) contain no `IsUnit` statement. No
existing declaration has this name or content. Mathlib's `MvPowerSeries.isUnit_iff_constantCoeff`
is the formal-series criterion, which is ruled out by 1 − X.

Records: the node differs from side-live only in `lean`. `lean.statement` occurs verbatim in the
file. Both stmt_deps are imported (public import of RestrictedSeriesPresentation; def-weil-field via
Mathlib `Field`). The plain imports are proof-leaf modules. All lines are ≤ 100 characters.
autoImplicit is off, and every variable and universe is bound. The only proof is `sorry`. The
docstring has the source place, `(blueprint: …)` and the four proof steps with their dependency ids.
No new definitions; no pro-étale content.
