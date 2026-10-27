## Worker report

The module `Sheaf.AlgebraicGeometry.CoordinateSubspaceBlowupCharts` states
`AlgebraicGeometry.CoordinateSubspaceBlowup.coordinate_subspace_blowup_charts`.
Its only theorem has proof `sorry`. The seven auxiliary abbreviations/definitions
specialize existing constructions to the coordinate ideal; they contain real data
and no postponed proof. No node statement or dependency list is changed.

The inherited BLOCKED ending concerned an unchanged stage-1 split. The current
assignment is stage 2, and the live node has a passing stage-1 review but no Lean
record. Thus the stage-handoff instruction in brief-stage2 section 0 applies;
this packet preserves that accepted split and supplies its first Lean statement.

Hypothesis and clause correspondence:

- An arbitrary commutative base ring is `(R : Type u) [CommRing R]`. There is
  no nontriviality, field, reducedness, Noetherian or characteristic assumption.
- The two nonnegative numbers are `(a b : ℕ)`.
- `A = R[x_1,...,x_a,y_1,...,y_b]` is `PolynomialRing R a b`, the existing
  `MvPolynomial (Fin a ⊕ Fin b) R`. The left summand indexes the x variables
  and the right summand the y variables. The zero-based indexing is merely a
  relabelling of the displayed one-based indices.
- `J = (y_1,...,y_b)` is `centerIdeal R a b`, literally the ideal span of
  the range of `fun j : Fin b ↦ MvPolynomial.X (Sum.inr j)`.
- `S = Spec R` is `Spec (.of R)`. `center R a b` is the quasi-coherent ideal
  sheaf corresponding to J, via `Scheme.IdealSheafData.ofIdealTop` and the
  canonical `Scheme.ΓSpecIso`. Thus M is the recorded global construction
  `(center R a b).blowup`, and its map to S is `(center R a b).blowupMap`
  followed by `Spec.map` of the constants map `R → A`.
- The positive-coordinate case is the implication `0 < b → ...`.
  Its `E` identifies the existing affine Rees blowup with this global glued
  blowup, with `E.hom ≫ blowupMap = AffineBlowup.toSpec ...`. This is the
  canonical affine description of the same scheme, not an extra hypothesis.
  The identification is part of the conclusion and is over `Spec A`.
- The standard chart `A[J/y_i]` is `ChartRing R a b i`, exactly
  `AffineBlowup.chartRing J y_i`, with no alternative chart algebra.
  `chartι` is the existing `AffineBlowup.chartRingι` specialized to the
  coordinate generator. Its composite with `E.hom` is therefore the standard
  chart in M. Open immersion follows from the existing chart instance and E's
  isomorphism. The cover is the equality
  `(⨆ i : Fin b, (chartι R a b i ≫ E.hom).opensRange) = ⊤`.
- The presentation ring is
  `MvPolynomial (ChartVariables a b i) R`, where
  `ChartVariables a b i = Fin a ⊕ (Unit ⊕ {j : Fin b // j ≠ i})`.
  The three summands give respectively the x variables, the single z variable,
  and the t variables with the i-th one omitted.
- The displayed R-algebra map being an isomorphism is expressed by the
  existence of `φ : ... ≃ₐ[R] ChartRing R a b i`, with all three prescribed
  assignments. For x, its value in the ambient localization is
  `algebraMap A _ (MvPolynomial.X (Sum.inl r))`. For z it is the image of
  `centerGenerator R a b i`, namely y_i. For each t_j it is the existing
  `AffineBlowup.chartFraction y_i 1 y_j`. Equality in the ambient localization
  determines equality in the chart subalgebra, whose inclusion is injective.
  By the polynomial universal property these assignments specify exactly the
  map in the node; this is not a claim about an unspecified ring isomorphism.
- The final part for each chart supplies an actual scheme isomorphism
  `c : Spec (.of (ChartRing ...)) ≅ AffineSpace (ULift (Fin (a+b))) (Spec (.of R))`
  and the equation saying its composite with the affine-space projection is
  `Spec.map` of `algebraMap R (ChartRing ...)`. Thus it is over S. `ULift`
  puts the finite coordinate set in the scheme's universe without imposing a
  size restriction. The chart map to S is this constants map by E's equation
  and `AffineBlowup.chartRingιOfEq_toSpec`.
- The zero-coordinate case is
  `b = 0 → centerIdeal R a b = ⊥ ∧ IsEmpty (center R a b).blowup`.
  The zero ideal is Mathlib's bottom ideal; `IsEmpty` of the scheme's point
  type says precisely that the scheme is empty.
- The last conjunction quantifies over every `(W : Scheme.{u})` and every
  `(e : W ⟶ (center R a b).blowup)`, assumes `Etale e`, and states `Smooth`
  of its composite with the canonical map M → Spec A → Spec R. It is outside
  both case implications, so includes b=0 and the identity/empty-source cases.
  No quasi-compactness condition is imposed on e.

Dependency declarations read and used:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map`, together with `Scheme.ΓSpecIso`.
- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial` and `MvPolynomial.algHom_ext`; the evaluation universal
  property is `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval`.
- `def-nagata-global-blowup`: `WeilConjectures.Blowup.Gluing`,
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and its `blowupMap`.
  `Scheme.IdealSheafData.ofIdealTop` is the existing Mathlib ideal-sheaf
  construction, not a new object chosen to satisfy the theorem.
- `def-nagata-blowup-chart-ring`:
  `WeilConjectures.Blowup.Affine.ChartAlgebra`,
  `AlgebraicGeometry.AffineBlowup.chartRing`, `chartFraction` and
  `homogeneousAwayEquivChart`. The already defined map `AffineBlowup.chartRingι`
  is read from `WeilConjectures.Compactification.StrictTransformChartModel`.
- `def-sbc-affine-space`: the Mathlib match `AlgebraicGeometry.AffineSpace`
  in `Mathlib.AlgebraicGeometry.AffineSpace`, with `AffineSpace.over` and
  `AffineSpace.SpecIso`/`SpecIso_inv_over` for the affine-base interpretation.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.

The stated proof dependencies are imported for stage 3:
`AffineBlowup.iSup_basicOpen_reesX_eq_top_of_span` from
`WeilConjectures.Blowup.FiniteDegree.Algebra`;
`AffineBlowup.chart` and `chart_toSpec` from
`WeilConjectures.Blowup.Affine.Defs`;
`Localization.Away` from the recorded Mathlib localization module;
`AffineSpace.smoothOfRelativeDimension_over` from
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`;
`MorphismProperty.arrow_mk_iso_iff` from
`Mathlib.CategoryTheory.MorphismProperty.Basic`;
`IsZariskiLocalAtSource.iff_of_iSup_eq_top` from
`Mathlib.AlgebraicGeometry.Morphisms.Basic`;
`smooth_and_fibre_dimension_zero_of_etale` from
`Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`; and
`AlgebraicGeometry.smooth_comp` from Mathlib's smooth-morphism module.
The theorem docstring gives all six proof steps of the accepted node.

Edge cases checked mathematically before writing:

- b=0: the span is empty, hence zero, and the blowup is empty rather than the
  ambient affine scheme. No chart index is invented in this case.
- b=1: the ratio-variable subtype is empty, leaving exactly a+1 variables;
  blowing up the coordinate Cartier divisor is consistent with this chart.
- a=0: the x equations are vacuous; the z and ratio equations remain present.
- R the zero ring: the polynomial and chart rings are zero rings and the
  spectra/affine spaces are empty. Every assertion still makes sense, with
  no hidden nonzero-element or nontrivial-ring binder.
- R nonreduced, e.g. Z/4: the denominator-clearing proof compares polynomial
  coefficients and never cancels a coefficient of R.
- Empty W and arbitrary non-quasi-compact etale W are included. The identity
  etale map recovers smoothness of M itself.

Searches for an existing exact statement:

- msearch leanfinder: "The blowup of affine space along a coordinate subspace
  has polynomial affine charts and every etale source is smooth over the base
  ring". Eight hits, concerning standard-smooth presentations and etale implies
  smooth, not a coordinate-subspace blowup chart theorem.
- msearch loogle: `"AffineBlowup", "MvPolynomial"`. Zero hits.
- msearch grep, Mathlib AlgebraicGeometry:
  `coordinate.*[Bb]low|[Bb]low.*coordinate`. Zero hits.
- rg over project `WeilConjectures` and `Sheaf` with the same coordinate/blowup
  pattern and the exact item id: upstream extension/strict-transform chart
  code and other Sheaf coordinate blowup lemmas, but no exact item theorem.
  The branch-drop theorem requires a regular Noetherian ambient ring, and the
  marked controlled chart theorem has additional marked-ideal/flag hypotheses;
  neither is this arbitrary-base polynomial theorem. The existing generic
  chart algebra, chart embedding, affine-space and blowup notions are reused.

Source read: `more-morphisms.tex`, remark-relative-blowup (0H1H), and
`divisors.tex`, lemma-blowing-up-affine (0804). The source explicitly allows
an arbitrary ring. The extra b=0 case follows from its zero-ideal chart
calculation, as required by the node. No statement dispute or correction.

Validation: the module compiled in both sandbox and library module modes via
the prescribed server scompile wrapper with no errors or non-sorry warnings.

## Second reading by Q154

No second reading by a worker: under the dispatch brief the worker delivers
directly, and the maintainer's independent review is the only second review.
