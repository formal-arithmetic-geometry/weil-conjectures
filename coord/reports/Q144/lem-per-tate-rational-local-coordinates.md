## Worker report

The module `Sheaf.RingTheory.TateRationalLocalCoordinates` states
`RestrictedSeries.tate_rational_local_coordinates`, with its sole proof `sorry`.
Its three auxiliary declarations have real data: `rationalValue` is coefficientwise
`tsum`, `rationalCoordinate` is the existing variable minus the existing constant,
and `rationalLocalAlgebra` is the constant ring map followed by the localization map.
They are notation/constructions for this node, not copies of existing notions.
The derivative is Mathlib's `MvPowerSeries.pderiv`, not a newly defined derivative.

Hypothesis and clause correspondence:

- The complete real-valued nonarchimedean field is `(F : Type u) [NormedField F]
  [IsUltrametricDist F] [CompleteSpace F]`. Nontriviality of the valuation is `hF :
  ∃ c : F, c ≠ 0 ∧ ‖c‖ ≠ 1`. No characteristic or discreteness assumption is imposed.
- The nonnegative integer number of variables is `(r : ℕ)`. The point is
  `(a : Fin r → F)` and the entire closed unit polydisc condition is `ha : ∀ i,
  ‖a i‖ ≤ 1`. Universes are explicit; coefficients and finite functions live at u.
- The actual Tate ring is Mathlib's `MvPowerSeries.IsRestricted.subring` at
  polyradius one. Its condition is coefficient norms tending to zero along the
  cofinite filter, precisely the finite-exception epsilon condition of the node;
  the inherited operations are coefficient addition and Cauchy multiplication.
- The ring homomorphism `ev` is asserted together with `HasSum` of the actual
  coefficient/monomial family for EVERY series. In a Hausdorff field this fixes ev
  uniquely as convergent evaluation. No arbitrary map or merely polynomial-level
  agreement is substituted for evaluation. `rationalValue` is its explicit scalar
  value by `tsum`; on a partial derivative its argument is the actual formal pderiv.
- The statement that the termwise derivatives are restricted is written explicitly
  using `MvPowerSeries.IsRestricted ... (MvPowerSeries.pderiv F i f.val)`.
  This makes the node's phrase 'termwise derivatives of restricted series' explicit;
  the coefficient formula in Mathlib is c_(ν+e_i)*(ν_i+1).
- `q = ker(ev)` is `RingHom.ker ev`. Its maximality is the existential proof binder
  immediately after ev, making its canonical prime-complement localization available.
  `RingHom.ker ev = Ideal.span (Set.range (rationalCoordinate a))` is exactly the
  coordinate-generator assertion.
- `R` is `Localization.AtPrime (RingHom.ker ev)`. The ideal `m = qR` is represented
  by `IsLocalRing.maximalIdeal R`; the exact identification is already Mathlib's
  `Localization.AtPrime.map_eq_maximalIdeal`, whose signature and docstring were read.
- `IsRegularLocalRing R` includes both `IsLocalRing R` and `IsNoetherianRing R` in
  its definition. It is the ring clause of `def-weil-regular-scheme`, not a new
  regularity predicate or the scheme-only declaration recorded for that node.
- The residue map is `ρ : R →+* F`, with `Function.Surjective ρ` and
  `RingHom.ker ρ = IsLocalRing.maximalIdeal R`. On every actual numerator and every
  denominator in `q.primeCompl`, `ρ (Localization.mk h v) = ev h / ev v.val`.
  Thus it realizes the residue field F, with the specified canonical normalization.
- `θ : (IsLocalRing.maximalIdeal R).Cotangent ≃ₗ[F] (Fin r → F)` gives the
  F-linear isomorphism on the genuine quotient m/m². The finite product is the
  finite direct sum F^{⊕r}. The scalar action is the actual composite constant and
  localization map, supplied by `rationalLocalAlgebra`.
- For EVERY fraction with numerator in q (`ev h = 0`) its cotangent class has
  ith coordinate `rationalValue a (MvPowerSeries.pderiv F i h.val) / ev v.val`.
  The `hm` binder is just the membership proof needed to type that fraction as an
  element of m; it always follows from the already asserted residue fraction formula
  and kernel equality. Thus it does not impose an extra mathematical hypothesis.
- The coordinate membership proofs `hy` are existentially SUPPLIED by the theorem.
  They are not assumed of the point or left as a potentially empty universal premise.
  For every vector b, `θ.symm b` is precisely the finite sum of b_i times the
  cotangent classes of the localized `x_i-a_i`.
- The explicit `r = 0 → Function.Bijective ρ` identifies R with F by its actual
  residue map in the zero-variable case. The target `Fin 0 → F` is the zero vector
  space, and θ identifies the source with that zero space. Empty sums are zero.

Dependency declarations read and used:

- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime`, with `AtPrime.isLocalRing` and `AtPrime.map_eq_maximalIdeal`.
  Also read the associated `Ideal.ResidueField` abbreviation and fibre-ring description;
  the item needs the localization and its actual residue map, not the fibre construction.
- `def-weil-regular-scheme`: its `mathlib_match` ring clauses are
  `IsRegularLocalRing` and `IsRegularRing` in `Mathlib.RingTheory.RegularLocalRing.Defs`.
  Read the complete class signature: regular local rings extend local and Noetherian
  rings. Read `Sheaf.AlgebraicGeometry.IsRegularScheme` too; its declaration is the
  separate locally-Noetherian scheme clause and is not used in this ring assertion.
- Added the already-landed definition node `def-trf-restricted-series-presentation`
  to `stmt_deps`: its module `Sheaf.RingTheory.RestrictedSeriesPresentation` supplies
  `RestrictedSeries.constants` on Mathlib's subring. The notion already exists, so no
  new definition node or dependency repair is made.
- `Mathlib.RingTheory.Ideal.Cotangent`: `Ideal.Cotangent` and `Ideal.toCotangent`,
  including its inherited module over any scalar ring acting on the ambient algebra.
- `Mathlib.RingTheory.MvPowerSeries.Derivative`: `MvPowerSeries.pderiv`, whose
  definition and full coefficient formula were read.
- Proof imports: `Sheaf.RingTheory.AffinoidPolynomialClosedPointComparison`,
  `RestrictedSeries.affinoid_polynomial_closed_point_comparison` (full signature read);
  `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`,
  `ringKrullDim_le_spanFinrank_maximalIdeal`; and
  `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
  The Gauss-completion and Banach-substitution proof nodes have no Lean records in
  the read DAG, so there is no recorded module to import for them. They are named
  in the proof docstring. They are proof prerequisites, not missing statement objects.

Source and edge checks:

Read Conrad's actual PDF at https://math.stanford.edu/~conrad/papers/aws.pdf,
Theorem 1.1.5(1), PDF page 4, and Exercise 1.2.8(3)-(4), PDF page 7. The first gives
Noetherianity and regularity; the exercise gives recentering at bounded rational points.
The explicit derivative coordinates are the node's agent-formulated Taylor consequence,
not falsely attributed as a displayed formula in Conrad. The existing seven-step proof
is preserved in the node and rendered in the theorem docstring.

Checked r=0 (empty exponents/variables/sums and canonical R≃F), r=1, the origin,
boundary coordinates with norm exactly one, and arbitrary positive characteristic.
In characteristic p the pth-power derivative vanishes as required, and the pth power
of a vanishing coordinate lies in m². Denominators have nonzero evaluation because
membership in `q.primeCompl` is precisely exclusion from the evaluation kernel.
No assumption that coordinates are topologically nilpotent is made. The zero-ring
case is excluded by the field hypothesis of the source, not by an added assumption.
The formula for a fraction in m needs no denominator derivative term because its
numerator evaluates to zero. No statement correction or dispute was necessary.

Searches actually made:

- `msearch.py ... leanfinder` with query 'The rational local ring of a Tate algebra
  is regular and its cotangent space is given by partial derivatives': 8 hits,
  including algebraic generators' cotangent bases and field cotangent-space vanishing;
  none is the rational Tate theorem.
- `msearch.py ... loogle` with query '"IsRegularLocalRing", "IsRestricted"': 0 hits.
- `msearch.py ... grep` with query
  'TateAlgebra|rational.*cotangent|IsRestricted.*eval': 0 hits.
- `msearch.py ... leansearch` with query 'restricted power series evaluation on
  bounded points partial derivatives Tate algebra': 8 hits; formal power-series
  evaluation and analytic-function derivatives, not the bounded Tate assertion.
  In particular `PowerSeries.aeval` requires topological nilpotence and does not
  give evaluation at unit-norm boundary coordinates.
- Direct `rg` of `lean/WeilConjectures` for restricted-series/Tate-algebra/local
  coordinate declarations found no match. The prescribed item-id grep also found none.
  Direct `rg` of `lean/Sheaf` found the existing RestrictedSeriesPresentation and
  AffinoidPolynomialClosedPointComparison modules, which are reused. The nearby
  NonarchimedeanSeriesSubstitution result is one-variable scalar substitution,
  not this local-ring statement. Full proposed declaration names were searched in
  Mathlib, upstream and Sheaf with no duplicate.
- Direct Mathlib search found `MvPowerSeries.pderiv` and its actual coefficient
  formula, so the draft's separate derivative-value helper was removed.
- `tools/blueprint_refs.py search 'restricted series'`: zero blueprint matches;
  ancestor lookup gave `lem-per-artin-gabber-affine-curve`. No new node is needed.
- The guessed unrecorded module `Sheaf.RingTheory.RestrictedSeriesGaussCompletion`
  was queried through `scompile.py --source` and reported unavailable. No declaration
  is invented for it, and it is not needed to type this statement.

Validation: the delivered file compiled cleanly through the prescribed `scompile.py`
server wrapper after replacing the derivative helper and making coordinate-class
membership and the r=0 normalization explicit. All variables/universes are explicit,
there is no local notation or private interface, and only the named main theorem
contains `sorry`. Final dry-run and delivery results are recorded by the delivery tool.

## Second reading by Q144

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
