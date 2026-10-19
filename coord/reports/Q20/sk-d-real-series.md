## Worker report

Existing declaration delivery; no module is added and no statement is changed.
The current blueprint unit is
`literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-d-real-series/_section.md`.
Its two advertised Lean names already exist in
`WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius`:

- `PowerSeries.radius`, lines 57–71 (docstring and definition).
- `PowerSeries.HasNonnegCoeffs`, lines 73–80 (docstring and definition).

The node has no statement or proof dependencies, so there are no dependency
records to repair. No repair note exists for this item.

Clause-by-clause comparison:

1. A complex formal series with coefficients indexed by nonnegative integers is
   `f : ℂ⟦X⟧`, with coefficient `PowerSeries.coeff n f`, `n : ℕ`.
   The existing `radius` accepts every such series by specializing `𝕜 := ℂ`.
   Its more general field binder imposes no additional hypothesis on this
   specialization: the standard complex normed-field instance supplies it.
2. The radius is `f.radius : ℝ≥0∞`. Its real-nonnegative arguments use `ℝ≥0`,
   and its value allows infinity. The definition applies
   `FormalMultilinearSeries.radius` to
   `FormalMultilinearSeries.ofScalars ℂ (fun n ↦ PowerSeries.coeff n f)`.
   `FormalMultilinearSeries.ofScalars_norm` identifies the coefficient norms
   with `‖PowerSeries.coeff n f‖`, the complex absolute values in the source.
   This is precisely the source supremum, although the underlying Mathlib
   definition uses bounded coefficients rather than summability directly.
   Indeed, `PowerSeries.summable_norm_coeff_mul_pow` gives summability for
   every `0 ≤ t < f.radius`. Conversely, if a candidate radius r has the
   source property, `PowerSeries.le_radius_of_summable` gives `t ≤ f.radius`
   for every nonnegative t < r, hence r ≤ f.radius. Taking suprema gives
   equality, including zero and infinity. No summability at the boundary
   is asserted or required. I read both existing theorem signatures and the
   underlying Mathlib radius definition and summability lemmas.
3. Nonnegative series are exactly `f.HasNonnegCoeffs`, defined by
   `∀ n, coeff n f ∈ Set.range ((↑) : ℝ≥0 → ℂ)`.
   Membership means equality to the image of a nonnegative real, so it
   includes the reality condition as well as nonnegativity, in every degree,
   including the constant term. It is not just nonnegativity of real parts.
4. The final sentence specifies standard operations, not an additional named
   object (the blueprint advertises only the preceding two definitions).
   Existing multiplication is the Cauchy coefficientwise product:
   `PowerSeries.coeff_mul` in `Mathlib.RingTheory.PowerSeries.Basic` states
   `coeff n (φ * ψ) = ∑ p ∈ Finset.antidiagonal n, coeff p.1 φ * coeff p.2 ψ`.
   Finite products use this multiplication. Formal exponential is Mathlib's
   `PowerSeries.exp ℂ`, whose nth coefficient is `1 / n!`; for a series g
   with zero constant term, `(PowerSeries.exp ℂ).subst g` is its formal
   exponential. `PowerSeries.HasSubst.of_constantCoeff_zero'` supplies the
   substitution condition, and `PowerSeries.coeff_subst'` gives its finite
   coefficient formula. These are in
   `Mathlib.RingTheory.PowerSeries.Exp` and `.Substitution`.
   For locally finite products with constant terms one, degreewise local
   finiteness says `∀ n : ℕ, Set.Finite {j | ∃ k ≤ n,
   PowerSeries.coeff k (f j - 1) ≠ 0}`. Thus each coefficient of finite
   partial products eventually stabilizes. Their product is the standard
   `∏' j, f j` in the coefficient topology, restricted to such families,
   and has precisely those stabilized coefficients. The existing
   `PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto` in
   `Mathlib.RingTheory.PowerSeries.PiTopology` expresses this coefficient
   interpretation. Arbitrary analytically convergent products are not being
   substituted for the locally finite products required in the source.
   These standard operations are reused, not redefined or postulated.

Edge cases checked by inspecting the definitions and the source:

- The zero series and every polynomial have infinite radius; zero is allowed
  as a nonnegative coefficient, and the zero series is nonnegative.
- Radius zero is allowed for rapidly growing coefficients, e.g. n!; the
  condition at candidate r = 0 is vacuous. At t = 0, the constant coefficient
  is the only possibly nonzero term, with the usual convention 0^0 = 1.
- The geometric series has radius one despite divergence at t = 1; the
  strict inequality in the source and summability lemma preserves this.
- A coefficient with nonzero imaginary part, or a negative real coefficient,
  fails HasNonnegCoeffs, even if its real part is nonnegative in the former
  case. There is no imposed constant-term-one condition on nonnegative series.
- Finite and empty product families satisfy local finiteness; the empty
  product is one. A family of factors 1 + X^m, m ≥ 1, is locally finite.
  Infinitely many repeated factors 1 + X fail local finiteness already in
  degree one. Formal exponential of zero is one; zero constant term of
  the argument is precisely the formal substitution condition over ℂ.

Searches made (the launcher records raw service responses in searches.jsonl):

- `msearch.py ... leanfinder` with query “radius of convergence of a complex
  formal power series and nonnegative coefficients”: eight hits about
  analytic/formal multilinear radii, no competing scalar-series definition.
- `msearch.py ... loogle` with query
  `PowerSeries.radius, PowerSeries.HasNonnegCoeffs`: zero hits, unknown
  identifier PowerSeries.radius in Mathlib's search environment.
- `msearch.py ... leansearch` with query “radius of convergence of formal
  power series”: eight hits, including FormalMultilinearSeries.radius,
  its scalar and summability interfaces; no competing PowerSeries definition.
- `msearch.py ... grep` with expression
  `radius|HasNonnegCoeffs|coeff_mul|HasProd` in RingTheory/PowerSeries:
  25 returned hits on multiplication, including Basic.lean:249 coeff_mul.
- `rg` for `PowerSeries.radius|HasNonnegCoeffs|sk-d-real-series` in the
  upstream WeilConjectures tree and the side lean/Sheaf tree found the exact
  two upstream definitions and their consumers, with no side duplicate.
  I read the complete upstream ConvergenceRadius module. Exact blueprint-id
  occurrences are the docstrings of these two definitions. Further Mathlib
  reads found exp, substitution, coefficient multiplication, and PiTopology.

No new nodes, dependency modules, node correction, or disputed statement.
The existing declaration signatures are checked by the prescribed delivery
wrapper's scompile probe; there is no newly delivered Lean file to compile.

## Second reading by Q20

Independent maintainer second reading of immutable delivery
`d8ac2fe2008d8ef5cb56357894986ffc4da6dd29`, performed on 2026-10-18.
This section replaces the delivery's placeholder; it is the maintainer's
reading, not a claim that another Q20 worker reviewed the delivery.

Read the immutable item record and worker report, the source place
`literature/blueprint/main-20261015/blueprint/sec-purity-real-sheaves/sk-d-real-series/_section.md`
(order 2948), and the entire existing module
`WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius`.
There are no statement dependencies, new nodes, dependency modules, or
statement corrections. The source text agrees with the immutable statement.

Clause and hypothesis checks:

1. `f : ℂ⟦X⟧` represents every complex formal series, with degrees in ℕ.
   Specializing the explicitly bound arbitrary field in `radius` to ℂ adds
   no hypothesis. Its universe is polymorphic, and ℂ has the required
   `NontriviallyNormedField` instance. No constant-term restriction is imposed.
2. Lines 70–71 define `radius` by the actual scalar formal multilinear series;
   no data or proof hole occurs in this definition. The recorded
   `lean.statement` is verbatim the signature before `:=`.
   Mathlib `Analysis/Analytic/OfScalars.lean:178` identifies the multilinear
   coefficient norm with the coefficient absolute value. Mathlib
   `Analysis/Analytic/ConvergenceRadius.lean:107` defines the bounded-coefficient
   supremum. Its lemmas at lines 233 and 241, and the scalar wrappers at
   upstream lines 87–97, identify it with the source supremum: every smaller
   nonnegative argument is summable, and summability implies the argument is
   at most the radius. Density of nonnegative reals gives the converse bound
   for each source candidate radius. This also covers infinity.
3. Lines 79–80 define `HasNonnegCoeffs` as membership of every coefficient in
   the image of ℝ≥0 in ℂ. This includes reality and nonnegativity, including
   degree zero, without demanding a constant term of one.
4. The last sentence specifies conventions for existing operations; the
   source advertises exactly the two attached definitions. Multiplication is
   the Cauchy product (`PowerSeries.coeff_mul`, Basic.lean:249). The exponential
   series has coefficients 1/n! (`Exp.lean:49–56`), and substitution into a
   zero-constant-term argument is valid (`Substitution.lean:67–69`), with
   finite coefficient support and formula at lines 230–251. For factors with
   constant term one, local finiteness in each degree means only finitely
   many factors differ from one through that degree. Finite partial-product
   coefficients therefore stabilize. In the scoped coefficient topology,
   `PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto`
   (`PiTopology.lean:101–108`) identifies their limit with the coefficientwise
   product. This convention retains the local-finiteness requirement; it
   does not replace it with arbitrary analytic multipliability.

Edge cases: zero and polynomials have infinite radius; factorial growth
allows radius zero; candidate radius zero is vacuous; t = 0 includes the
constant coefficient with 0^0 = 1. The geometric series has radius one even
though it diverges at the boundary. Negative real and nonreal coefficients
fail nonnegativity. Empty and finite products are allowed, with empty product
one. Factors 1 + X^m for m ≥ 1 are locally finite; repeated factors 1 + X are
not. The exponential of zero is one. There is no restriction on an indexing
universe for the product convention.

Independent searches used `rg` for `HasNonnegCoeffs`, `def radius`, and the
blueprint id in the upstream WeilConjectures tree, the group lean/Sheaf tree,
and Mathlib's PowerSeries tree. They recover the attached definitions and
upstream consumers, with no side duplicate. The worker report records
LeanSearch, LeanFinder/Loogle, and grep searches. No new definition is needed.

The existing module and declaration docstrings describe the radius and name
`sk-d-real-series`; their old upstream format does not use the new side-module
`Source: ... (blueprint: ...)` template. No module is delivered or edited,
so no upstream documentation rewrite is imposed. One upstream explanatory
sentence incorrectly calls boundedness at r equivalent to summability at
all t < r. For example a_n = n at r = 1 disproves that pointwise equivalence.
The two suprema still agree by the lemmas above; neither the actual definition
nor the worker report's supremum argument depends on this erroneous sentence.

Compiler reproduction: ran the prescribed command
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q20 sk-d-real-series /home/ubuntu/weil-src-slopmaster2/WeilConjectures/Mathlib/Analysis/Analytic/ConvergenceRadius.lean`.
It exited 0, with clean sandbox and library checks (2.7 s and 2.8 s), no
warnings or errors. The installed wrapper currently uses the server side
overlay and wire confirmation rather than a local overlay. No direct ssh,
global build, live Lean write, or repository mutation was performed. There
is no newly delivered Lean file; this independently reproduces compilation
of the existing module beyond the worker's unaccompanied probe assertion.

Findings: mathematical binding accepted unchanged. H1/H11 report defect
fixed by replacing the empty second-reading section with this substantive
reading. No H3/H4/H5/H6/H7/H9/H10/H12/H13 defect found. Existing upstream
proofs were read as context and were not added as stage-2 local proofs.
No pro-etale substitute, missing-helper repair, universe repair, or citer
audit is implicated.
