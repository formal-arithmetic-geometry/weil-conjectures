## Worker report

The new module `Sheaf.TraceFormula.FormalBinaryMorse` states
`MvPowerSeries.formal_binary_morse` with `sorry`. It defines no new notion and
changes only the item's `lean` record. The existing Q50 delivery was a stage-1
split, with no Lean declaration, so this stage-2 packet supplies the missing
statement rather than redelivering the unchanged split.

The source read is `literature/stacks-project/curves.tex`, Tag 0C49,
`lemma-nodal-algebraic`, proof of (2) implies (3), together with the discussion
of nondegeneracy immediately before that lemma. The node applies exactly that
successive-correction calculation to a single series before quotienting. The
module docstring records all five steps of the node's proof, including the
fixed identity `f = Q(x_r,y_r) + E_r` and the final inversion `α = β⁻¹`.

Hypotheses and objects:

- `(F : Type u) [Field F]` is an arbitrary field, with an explicitly bound
  universe and no characteristic restriction.
- `(f : MvPowerSeries (Fin 2) F)` supplies `S = F[[u,v]]` and its specified
  element. `MvPowerSeries.X 0` and `MvPowerSeries.X 1` are `u` and `v`.
- `(a b c : F)` supplies all three coefficients of the quadratic part.
- The ideal `Ideal.span (Set.range (MvPowerSeries.X : Fin 2 →
  MvPowerSeries (Fin 2) F))` is exactly `(u,v)` because the variable index
  type is `Fin 2`. It is written out wherever the signature needs it.
- `hfp` states `f ∈ p ^ 2`.
- `hquad` states `f - Q ∈ p ^ 3`, where `Q` is
  `C a * X 0 ^ 2 + C b * X 0 * X 1 + C c * X 1 ^ 2`. Given `f ∈ p²`, this
  is precisely the assertion that its homogeneous degree-two part is `Q`:
  the variable-ideal powers consist of series with all coefficients below
  that total degree zero. No condition is imposed on higher coefficients.
- `hdisc` is the literal inequality `b ^ 2 - 4 * a * c ≠ 0`.

Conclusion, clause by clause:

- `∃ α : S ≃ₐ[F] S` supplies an `F`-algebra automorphism, including its
  inverse and its action on constants.
- `@Continuous _ _ p.adicTopology p.adicTopology α` is continuity for the
  explicitly specified topology on both copies of `S`. Mathlib's
  `Ideal.hasBasis_nhds_zero_adic` states that this topology has the sets
  `p ^ N` as a basis of zero-neighbourhoods. There is no coefficient-field
  topology binder and no reliance on a product-topology instance.
- The next conjunct is `α (X 0) - X 0 ∈ p ^ 2`.
- The following conjunct is `α (X 1) - X 1 ∈ p ^ 2`.
- The last conjunct is `α f = Q`, with exactly the same quadratic expression
  as in `hquad`. The direction is the node's direction, from `f` to `Q`.

Dependency declarations read and used:

- Statement dependency `def-weil-pbc-multivariate-power-series`: Mathlib's
  `MvPowerSeries` in `Mathlib.RingTheory.MvPowerSeries.Basic`, whose data is
  `(σ →₀ ℕ) → R`, with coefficientwise addition and the Cauchy product.
  The declaration and its docstring were read in the pinned source. The
  theorem uses this existing construction directly.
- Mathlib's `Ideal.span`, ideal powers, `AlgEquiv`, `Continuous`, and
  `Ideal.adicTopology` supply the other standard interfaces. The adic
  topology's declaration and neighbourhood-basis theorem were read in
  `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology`.
- Proof dependency `lem-weil-pbc-power-series-field-cohen-regular-complete`:
  `MvPowerSeries.power_series_field_cohen_regular_complete` in
  `Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete` (private import).
- Proof dependency `lem-weil-pbc-nakayama-local-generators`: Mathlib's
  `IsLocalRing.map_mkQ_eq_top` in `Mathlib.RingTheory.LocalRing.Module`
  (private import), as its `mathlib_match` records.
- Proof dependency `def-weil-pbc-regular-system-of-parameters`:
  `IsLocalRing.IsRegularSystemOfParameters` in
  `Sheaf.RingTheory.IsRegularSystemOfParameters` (private import).
- Proof dependency `lem-weil-pbc-power-series-full-coordinates-field`:
  `MvPowerSeries.exists_algEquiv_full_parameters_field` in
  `Sheaf.RingTheory.PowerSeriesFullCoordinatesField` (private import).

Edge cases checked: for `f = Q`, the identity automorphism has the required
properties. In characteristic two, `f = uv + u³`, `a = c = 0`, `b = 1` meets
the hypotheses, and `u ↦ u`, `v ↦ v - u²` sends `f` to `uv` while fixing
both variables modulo `p²`. In characteristic two, `u² + v²` has zero
polar discriminant and is correctly excluded. The case `Q = 0` is also
correctly excluded. For characteristic zero, `u² + v² + v³` meets the
hypotheses with nonzero discriminant. The continuity topology includes
`N = 0` (the whole ring) and all higher ideal powers.

Searches made through the required wrapper:

- `msearch.py Q17 lem-trf-formal-binary-morse leanfinder "A formal power
  series in two variables with nondegenerate quadratic leading term is
  transformed into that quadratic by a formal coordinate automorphism"`:
  eight results about Weierstrass changes and division; no formal Morse
  normalization.
- `msearch.py Q17 lem-trf-formal-binary-morse loogle "MvPowerSeries,
  AlgEquiv"`: twelve results, including `renameEquiv`, `isEmptyEquiv`,
  `optionEquivLeft`, and `finSuccEquiv`; none states the item.
- `msearch.py Q17 lem-trf-formal-binary-morse grep
  "Morse|quadratic|hessian|nondegenerate" RingTheory/MvPowerSeries`:
  zero hits.
- `msearch.py Q17 lem-trf-formal-binary-morse leansearch "Formal Morse
  lemma power series with invertible Hessian is right equivalent to its
  quadratic term"`: eight analytic calculus/Taylor-series results; no
  formal-ring result.
- `rg -n -i 'morse|hessian|nondegenerate.*quadratic|formal_binary_morse|
  lem-trf-formal-binary-morse'` over the upstream `WeilConjectures/`,
  `lean/Sheaf/`, and `dag/lean_names_upstream.json`: no existing item
  declaration; only references in the formal Jacobian and nodal-point
  statement modules. The item-ID search of upstream likewise found none.
- Mathlib's `RingTheory/Polynomial/Morse.lean` was inspected: it concerns
  Galois groups of univariate polynomials and does not state this result.

No new nodes, dependency repairs, statement correction, disputed statement,
or mathematical node fault was needed. The compiler found missing public
imports in the first draft; those were repaired. The preflight found that
`lean.statement` must stop before `:=`, and that the literal blueprint tag
must be on one line; both were repaired. The UTC date in the record was
obtained from `date -u +%F`.

## Second reading by Q17

Author's own rereading, under the dispatcher's instruction to deliver
personally and start no other agents; independent review belongs to the
maintainer. I reopened the node and module and checked each item above:
`F`, `S`, `u,v`, `p`, `f ∈ p²`, `f-Q ∈ p³`, and the discriminant are all
present with their stated objects; the conclusion contains one continuous
`F`-algebra automorphism, both tangent conditions, and `α(f)=Q`. I replaced
the initial explicit zero-neighbourhood quantifier with Mathlib's actual
`Continuous` and `Ideal.adicTopology` interfaces, completed the proof
plan step by step, and added the four available proof-only imports. The
statement has no characteristic assumption or auxiliary coordinate data.
The sole postponed theorem is the DAG node's theorem itself. Definitions
with postponed data, file-local aliases, auto-bound variables, and extra
lemmas are absent.
