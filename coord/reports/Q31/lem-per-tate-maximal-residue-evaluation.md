## Worker report

The module `Sheaf.RingTheory.TateMaximalResidueEvaluation` states
`RestrictedSeries.tate_maximal_residue_evaluation`. Its only theorem has proof
`sorry`. The two helper definitions contain real data: `tateResidueScalar` is
`(Ideal.Quotient.mk n).comp (RestrictedSeries.constants F r)` and
`tateResidueCoordinate` is the quotient of the actual formal variable. Neither
helper chooses a map or assumes evaluation. Both belong to the canonical
quotient maps of this node, and are listed in `lean.declarations`.

Source read: Conrad, *Several approaches to non-archimedean geometry*,
https://math.stanford.edu/~conrad/papers/aws.pdf, PDF pp. 2--4, §1.1:
the preliminary finite-extension paragraph, Definition 1.1.2, Exercise 1.1.4,
Theorem 1.1.5(1), and its following paragraph. The latest blueprint ancestor
`lem-per-artin-gabber-affine-curve.proof.md` was read; as the accepted split
records, its current Step 3 discusses duality, while this node is a generic
analytic prerequisite on the inherited formal-algebraization branch. The
natural-language statement and accepted proof split are unchanged.

Hypotheses and clauses, in order:

- The field F with its real multiplicative absolute value is `[NormedField F]`;
  nonarchimedeanness is `[IsUltrametricDist F]`; completeness is
  `[CompleteSpace F]`; nontriviality of the absolute value is the explicit
  `hF : ∃ c : F, c ≠ 0 ∧ ‖c‖ ≠ 1`. This does not assume discreteness,
  local compactness, characteristic zero, perfection, or separability.
- The number of variables is `r : ℕ`, including zero. The ring is precisely
  `MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))`.
  Mathlib's `IsRestricted` says its weighted coefficient norm tends to zero
  along the cofinite filter. Radius one makes this exactly the finite-above-
  every-positive-epsilon condition. Its operations are those of
  `MvPowerSeries`, hence coefficientwise addition and finite Cauchy products.
- `n : Ideal` of that subring, with `[n.IsMaximal]`, is the maximal proper
  ideal. Every occurrence of L in the conclusion is the actual ring quotient
  by n, not a separate field with an arbitrary map or an assumed presentation.
- Finite degree is the existing `Module.Finite` applied to the module of the
  actual algebra `(tateResidueScalar F r n).toAlgebra`. In particular the
  scalar action is induced by constant series and the actual quotient map.
- The extending absolute value is existentially supplied as
  `v : AbsoluteValue (restricted-series-ring ⧸ n) ℝ`.
  `∀ c : F, v (tateResidueScalar F r n c) = ‖c‖` expresses extension.
  `IsNonarchimedean v` expresses the strong triangle inequality, and
  `@CompleteSpace _ v.toNormedRing.toUniformSpace` expresses completeness
  for precisely its norm metric. `AbsoluteValue.toNormedRing` uses the
  existing quotient ring operations and the norm x ↦ v x.
- Uniqueness quantifies over EVERY `w : AbsoluteValue L ℝ` extending the
  base norm and concludes `w = v`. It does not assume in advance that w
  is complete, bounded on coordinates, or nonarchimedean. Thus uniqueness
  is of the extending absolute value itself.
- The actual a_i are `tateResidueCoordinate F r n i`. The clause
  `∀ i : Fin r, v (tateResidueCoordinate F r n i) ≤ 1` gives all bounds.
- For every actual restricted series h, `HasSum` states that the terms
  `tateResidueScalar F r n (MvPowerSeries.coeff ν h.val) *
  ν.prod (fun i e ↦ tateResidueCoordinate F r n i ^ e)` converge to
  `Ideal.Quotient.mk n h`. The topology is explicitly that induced by v,
  and `SummationFilter.unconditional (Fin r →₀ ℕ)` takes the limit over
  all finite sets of multi-indices. Thus this asserts convergence and the
  value, without using the default value of a possibly divergent `tsum`.
- The final clause `r = 0 → n = ⊥ ∧ Function.Bijective
  (tateResidueScalar F r n)` gives n = 0 and the canonical identification
  F ≅ L. Bijectivity of the named ring homomorphism is precisely existence
  of its inverse ring isomorphism; it is not a literal type equality.

Dependency declarations used:

- `def-weil-finitely-generated-module`: `Module.Finite`,
  `Mathlib.RingTheory.Finiteness.Defs`; its full class signature and docstring
  were read. It is finite generation, not finiteness of the underlying set.
- Added the already landed `def-trf-restricted-series-presentation` to
  `stmt_deps`, because its existing declaration `RestrictedSeries.constants`
  in `Sheaf.RingTheory.RestrictedSeriesPresentation` is used by the canonical
  scalar map. The full module and recorded declarations were read, including
  its use of `MvPowerSeries.IsRestricted.subring`. No new notion is defined.
- Mathlib's `Ideal.Quotient.mk`, `RingHom.toAlgebra`, `AbsoluteValue`,
  `AbsoluteValue.toNormedRing`, `IsNonarchimedean`, and `HasSum` provide the
  remaining standard structures. No field structure is assumed as additional
  data on the quotient; maximality is already a hypothesis.

Proof imports (plain imports) cover the currently recorded declarations:
`TensorProduct`/`TensorProduct.lift` from
`Mathlib.LinearAlgebra.TensorProduct.Basic`;
`AlgHom.norm_apply_le_self` from `Mathlib.Analysis.Normed.Algebra.Spectrum`;
`FiniteDimensional.complete` from
`Mathlib.Topology.Algebra.Module.FiniteDimension`;
`spectralNorm_unique_field_norm_ext`, `spectralNorm.normedField`,
`spectralNorm.normedSpace`, `isNonarchimedean_spectralNorm`, and
`spectralNorm_extends` from `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`;
`Algebra.IsIntegral.of_finite` from
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic`.
The proof nodes `lem-per-tate-finite-scalar-extension`,
`lem-per-tate-triangular-distinguished-coordinate`,
`lem-trf-restricted-series-gauss-completion`, and
`lem-trf-tate-weierstrass-norm-division` have no recorded Lean module on the
read base, so there is no module to import for these proof-only dependencies.
Their mathematical steps are included in the theorem docstring. They are
not hypotheses of this theorem.

Edge checks: for r = 0, `Fin 0 →₀ ℕ` has exactly the zero exponent, the
monomial product is 1, and the sum is the constant coefficient; the explicit
last clause identifies the quotient with F and n with zero. Constant series
and h = 0 have the correct evaluation; coordinate images of norm exactly 1
are permitted. The zero quotient is excluded exactly by maximal properness.
Arbitrary characteristic and inseparable finite extensions remain covered.
All universes and variables are explicitly bound, with both automatic-
implicit options disabled. There is no statement correction or disputed clause.

Searches actually run with msearch.py under Q31 and this item:

- leanfinder: "Maximal residue fields of a Tate algebra are finite extensions
  and the quotient is convergent evaluation at coordinates of norm at most one".
  Eight hits, including `PowerSeries.residueFieldOfPowerSeries`, valued-field
  residue fields, and compact-local-ring residue finiteness. None is the
  Tate maximal-residue-field/evaluation theorem.
- loogle: `"TateAlgebra"`. Zero hits.
- grep: `TateAlgebra|RestrictedPowerSeries|restricted.*maximal|tate.*residue`.
  Two unrelated Mathlib hits (finite adeles and L-series); no match.
- leansearch: "Restricted multivariate power series subring at radius one
  maximal ideal finite degree residue field evaluation". Eight hits include
  `MvPowerSeries.hasSum_aeval`, `MvPowerSeries.HasEval`, and formal-series
  evaluation. These do not assert residue finiteness or the coordinate bounds
  and do not give restricted evaluation for points of norm exactly one.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for `TateAlgebra`,
  `tateAlgebra`, `RestrictedSeries`, `restrictedSeries`, and maximal evaluation:
  found the existing `RestrictedSeriesPresentation` and
  `AffinoidPolynomialClosedPointComparison` interfaces. The latter was read
  in full: it states ideal closedness, Noetherianity and completed local-ring
  comparisons, not this theorem. No duplicate theorem was found.
- rg for the exact node id in `lean/WeilConjectures`: no hit. The proposed
  declaration name was also searched with no existing match.

Verification: scompile.py compiled both the sandbox and final library module
cleanly. An initial elaboration probe exposed that `Ideal.Quotient.field` is
an explicit abbrev, not an automatic field instance. The final statement uses
`AbsoluteValue.toNormedRing` for its induced metric, which needs only the
already present quotient ring structure. An explicit unconditional summation
filter also supplies the optional final parameter of the fully explicit
`@HasSum` application. No local instances or statement-level lets are used.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
