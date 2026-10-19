## Worker report

This is an existing-declaration delivery. No Lean module, definition, or theorem is added.
The item `d-real-series` and its sole statement dependency `sk-d-real-series` have identical
statements. I read both complete node records, the dependency's Lean record, the full upstream
module, and both definition docstrings and bodies. The declarations recorded here are the same
ones already recorded and reviewed on that dependency:

- Module `WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius`,
  `PowerSeries.radius`, source lines 57–71 (signature and body at 70–71).
- Same module, `PowerSeries.HasNonnegCoeffs`, source lines 73–80
  (signature and body at 79–80).

Sources read: the item's master-snapshot `sk-d-real-series/d-real-series.md`, and the current
`literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-d-real-series/`
`_section.md` and `d-real-series.md`. All three give the same mathematical text. The current
section explicitly attaches `PowerSeries.radius` and `PowerSeries.HasNonnegCoeffs` to it.
There is no blueprint update requiring a different statement, and no repair note for this item.

Clause-by-clause correspondence:

1. `f(T) = ∑ a_n T^n ∈ ℂ[[T]]`: instantiate the existing radius definition's coefficient
   field `𝕜` with `ℂ` and its argument with `f : PowerSeries ℂ`; `a_n` is
   `PowerSeries.coeff n f`. `NontriviallyNormedField ℂ` is the existing canonical instance,
   so this introduces no additional mathematical hypothesis. The general upstream definition
   includes the required complex specialization, without replacing it by a special subclass.
2. `R(f)`: `PowerSeries.radius f : ℝ≥0∞`, defined as
   `(FormalMultilinearSeries.ofScalars ℂ (fun n ↦ PowerSeries.coeff n f)).radius`.
   The extended nonnegative reals retain radius zero and infinite radius. This is genuine
   existing data, with no postponed choice or proof.
3. The supremum over `r ≥ 0` such that the norm series converges for every `0 ≤ t < r`:
   nonnegative real test radii are `t : ℝ≥0`, and the summability statement is
   `Summable (fun n ↦ ‖PowerSeries.coeff n f‖ * (t : ℝ) ^ n)`.
   `PowerSeries.summable_norm_coeff_mul_pow` gives this for `(t : ℝ≥0∞) < f.radius`.
   Conversely `PowerSeries.le_radius_of_summable` makes each such summable `t` at most
   `f.radius`. If all `t < r` are summable and `f.radius < r`, choose a real `t` strictly
   between them to obtain a contradiction. Hence each admissible `r` is at most `f.radius`.
   For the other inequality, every finite `r ≤ f.radius` is admissible by the first theorem;
   their supremum is `f.radius`, including when it is infinite. Thus the existing definition
   equals the blueprint's supremum. Complex norm is exactly the absolute value in the text.
4. Nonnegative coefficients: `PowerSeries.HasNonnegCoeffs f` unfolds to
   `∀ n, PowerSeries.coeff n f ∈ Set.range ((↑) : ℝ≥0 → ℂ)`.
   Membership says the coefficient is the image of a nonnegative real, imposing both zero
   imaginary part and nonnegative real part. It does not merely bound a complex norm.
5. Products defined coefficientwise: the existing `PowerSeries` multiplication has
   `PowerSeries.coeff_mul` in `Mathlib.RingTheory.PowerSeries.Basic`:
   the degree `n` coefficient is the finite sum of `coeff i f * coeff j g` over `i + j = n`.
   No constant-term restriction is needed for this finite Cauchy product.
6. Exponentials with the requisite constant terms: `PowerSeries.exp ℂ` in
   `Mathlib.RingTheory.PowerSeries.Exp` has coefficient `1 / n!`.
   For `h : PowerSeries ℂ` with `constantCoeff h = 0`, its formal exponential is
   `(PowerSeries.exp ℂ).subst h` using `Mathlib.RingTheory.PowerSeries.Substitution`.
   `PowerSeries.HasSubst.of_constantCoeff_zero'` supplies the substitution condition;
   `coeff_subst_finite'` and `coeff_subst'` express degreewise finite coefficient sums.
   This is the formal exponential convention, not an assumption of analytic convergence.
7. Infinite products required to be locally finite in each degree: this last sentence
   restricts which families are used in formal products; it does not introduce another
   named invariant alongside radius and nonnegativity. For factors `1 + h_i`, the restriction
   means for each degree bound `N` only finitely many factors have a nonzero term of `h_i`
   in degrees at most `N`. Consequently finite partial products have eventually constant
   coefficients through degree `N`, and their coefficientwise limit is the formal product.
   It is represented by the existing infinite-product operation in the power-series product
   topology, used only on these locally finite families. Mathlib's
   `PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top`
   in `Mathlib.RingTheory.PowerSeries.PiTopology` explicitly handles the usual ordered-family
   case by orders tending to infinity. Mere `Multipliable` is not asserted to be equivalent
   to local finiteness, and is not substituted for the stated restriction.

The final operation conventions are supplied by existing Mathlib constructions, exactly as in
`sk-d-real-series`'s reviewed record. They require no additional definition node or dependency
repair. No statement, statement dependency, proof, or proof dependency of the item is changed.

Edge cases checked before recording the declarations:

- The zero series and every polynomial have infinite radius (the upstream `radius_coe`
  covers polynomials); zero coefficients satisfy the nonnegative predicate.
- Series with radius zero remain included: `r = 0` has an empty interval of tests, and
  no positivity assumption on the radius appears. The actual norm series at `t = 0`
  has only its constant term, using `0^0 = 1`.
- At a finite positive radius there is no assertion of convergence on the boundary.
  The geometric series has radius one and diverges at one. The supremum is unchanged
  whether or not convergence happens at an endpoint.
- A non-real coefficient, even one with nonnegative real part, fails `HasNonnegCoeffs`.
  A negative real coefficient fails too; zero is allowed.
- `exp(0)` is one and the exponential constant term is one. A series with nonzero
  constant term is not silently treated as a degreewise finite formal substitution.
- An empty product is one, and a finite product satisfies the local-finiteness convention.
  Infinitely many factors contributing in a fixed bounded degree are not admitted by that
  convention merely because their complex coefficients might converge analytically.

Upstream documentation caveat: its radius docstring says boundedness of `‖a_n‖ r^n` at
one endpoint `r` is equivalent to summability at all `t < r`. The reverse implication at
the same endpoint is too strong: `a_n = n`, `r = 1` is a counterexample. This does not
invalidate the definition or the match: the two supremums agree by the strict-interior
argument in clause 3, using the actual theorem signatures read in the module. I do not use
the erroneous endpoint equivalence. No mathematical fault in the item's statement was found;
no STATEMENT-DISPUTED flag or statement correction is required.

Searches performed (all with group Q125 and item d-real-series):

- `msearch.py ... leanfinder "formal complex power series radius of convergence supremum
  nonnegative coefficients coefficientwise multiplication exponential locally finite infinite
  product"`: eight hits, including formal multilinear radii, analytic exponential results,
  and `PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top`.
  No replacement for the upstream pair of definitions.
- `msearch.py ... loogle "PowerSeries.radius, PowerSeries.HasNonnegCoeffs, PowerSeries.exp,
  PowerSeries.coeff_mul"`: zero hits; service reports unknown `PowerSeries.radius`.
  The upstream extension must be inspected directly rather than inferred absent.
- `msearch.py ... leansearch "radius of convergence of a complex formal power series and
  nonnegative coefficients"`: eight hits, including `FormalMultilinearSeries.radius`,
  scalar radius bounds, and analytic-radius results; no competing PowerSeries pair.
- `msearch.py ... grep "def radius|def HasNonnegCoeffs|def exp|theorem coeff_mul|
  multipliable_one_add" RingTheory/PowerSeries`: nineteen hits, including `exp`,
  `coeff_mul`, and the infinite-product theorem; no radius/nonnegative predicate there.
- `rg` of `real.series|real_series|RealSeries|real-series` in upstream `WeilConjectures`
  found both blueprint docstrings in `ConvergenceRadius.lean`. The equivalent node-id
  search finds those same declarations. Direct searches for the definition names confirm
  their signatures and bodies. `dag/lean_names_upstream.json` had no additional match.
- `rg` of `PowerSeries.(radius|HasNonnegCoeffs)|namespace PowerSeries` in `lean/Sheaf`
  found unrelated PowerSeries modules and no competing definitions of this notion.
  Read the existing exponential-substitution module as confirmation of the convention.
- Mathlib `rg` in `RingTheory/PowerSeries` and `Analysis/Analytic/ConvergenceRadius.lean`
  located the exact multiplication, exponential, substitution, and scalar-radius interfaces
  used in the explanation above; their signatures and relevant docstrings were opened.

Validation: an import-and-`#check` scratch file, kept outside the delivery modules, compiled
cleanly through the prescribed `scompile.py`, checking both upstream definitions and the cited
Mathlib interfaces. This delivery adds no modules requiring separate compilation. The required
`deliver2.py Q125 d-real-series --no-push` passed: the existing-declaration probes compiled
and server preflight returned OK; only this node file and this report were staged.

## Second reading by Q125

I made a separate clause-by-clause rereading with the node, both upstream definitions,
the current blueprint section, and the Mathlib operation signatures open. No other agent
was started, following the dispatcher's explicit instruction. This section records that
second pass and does not claim an independent worker's review.

The complex series in the node matches the `𝕜 = ℂ` specialization of `radius` and the already
complex argument of `HasNonnegCoeffs`. The nonnegative test radii and strict inequalities
match the two summability interfaces; the strict-interior argument gives the stated supremum
without the upstream docstring's endpoint overstatement. Both zero and infinite radius are
retained. The range predicate forces coefficients to be real and nonnegative, rather than
merely asserting nonnegative real parts. Multiplication is the antidiagonal Cauchy sum;
exponentiation is the factorial series substituted only with the requisite zero constant
term; local finiteness remains a restriction on the families used in formal infinite products.
I checked the empty-product, constant-term, and boundary cases above. These conventions
introduce no new object that needs a duplicate definition. The item's dependency records
exactly these existing declarations for the textually identical statement.

The only mismatch found was explanatory wording in the upstream radius docstring, not its
Lean definition or this node's statement. The report explicitly replaces that argument with
the valid supremum comparison. No source, statement, dependency record, or Lean module
was changed; the item's only delta is its `lean` binding.
