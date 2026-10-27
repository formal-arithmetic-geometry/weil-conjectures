## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralBlowupChartDensity` states
`AlgebraicGeometry.Scheme.IdealSheafData.integral_blowup_chart_density` with one
`sorry` and no new definitions. The node is unchanged except for `lean`.

Hypotheses and clauses, in node order:

- An integral scheme T is `{T : Scheme.{u}} [IsIntegral T]`.
- The quasi-coherent ideal is `I : T.IdealSheafData`, Mathlib's compatible ideal
  data on all affine opens. Its actual ideal module is the existing `I.toModules`.
  `hI : I ≠ ⊥` says it is nonzero; `hfinite : I.toModules.IsFiniteType` is the
  finite-type condition of pqf-def-coherent. Quasi-coherence is inherent in the
  ideal datum, so no stronger coherence or Noetherian assumption is imposed.
- The ordinary glued blowup and structure map are exactly `I.blowup` and
  `I.blowupMap` from the recorded global-blowup dependency.
- The closed proper-stalk locus is `I.support`; `U` is `I.support.compl`.
  The docstring and proof of the recorded
  `Scheme.quasi_coherent_ideal_zero_set_affine` identify support with the points
  where the inclusion of the ideal stalk is not surjective. Thus this is the
  node's V(I), not the nonzero-stalk support of the ideal module.
- The first three conclusions are `Nonempty I.support.compl`,
  `Dense (I.support.compl : Set T)`, and integrality of
  `Scheme.Opens.toScheme (X := T) I.support.compl`.
- `∀ V : T.affineOpens, Nonempty V.1 → I.ideal V ≠ ⊥` gives the nonzero affine
  section ideal on every nonempty affine open; its ring is exactly `Γ(T,V.1)`.
- The affine comparison over V is the canonical open immersion `I.blowupι V`.
  `IsPullback (I.blowupNatTrans.app V) (I.blowupι V) V.1.ι I.blowupMap`
  and the equality of its open range with `I.blowupMap ⁻¹ᵁ V.1` express the
  identification of open subschemes over V, not merely a bijection of points.
  Its source is definitionally `AffineBlowup (I.ideal V)`, itself Proj of the
  Rees algebra, and its map to V is `toSpec` followed by `V.2.isoSpec.inv`.
- Compatibility on smaller affine W is the equality
  `I.blowupFunctor.map (homOfLE hWV) ≫ I.blowupι V = I.blowupι W` for W ≤ V.
  The functor map is exactly the affine blowup map induced by section restriction,
  with `I.map_ideal hWV`; it is not an arbitrary choice of comparison maps.
- Every choice of generators `(f_0,...,f_r)` is quantified as
  `r : ℕ`, `f : Fin (r+1) → I.ideal V` and
  `Ideal.span (Set.range fun i ↦ (f i : Γ(T,V.1))) = I.ideal V`.
  The subtype simply packages membership of each generator; repetitions and
  zero generators are allowed. The supremum of the open ranges of
  `AffineBlowup.chartRingι (I.ideal V) (f i).2` is top.
- These canonical open immersions have source `Spec` of the recorded
  `AffineBlowup.chartRing (I.ideal V) (f i)`, literally the subalgebra of the
  localization away from f_i. Their composites with `toSpec` are explicitly
  `Spec.map` of the canonical algebra map, giving the cover over V.
- The zero-generator implication states `IsEmpty` of the chart spectrum.
- The nonzero-generator implication states `IsDomain` of that very subalgebra
  (which includes nontriviality). Pulling the inverse image of U back through
  the canonical chart embedding into the global blowup is exactly
  `PrimeSpectrum.basicOpen (algebraMap _ _ (f i))`. Equality of opens also
  identifies their restricted structure sheaves.
- The same principal open has a nonempty underlying set and is dense in its
  chart spectrum. The last existential supplies a nonzero generator and a
  nonempty chart for every chosen generating family over every nonempty V.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`, with
  nonemptiness and domain sections on every nonempty open.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the recorded
  `Scheme.Modules.IsQuasiCoherentFiniteType` and its exposed constituent
  `SheafOfModules.IsFiniteType`; only the finite-type constituent is needed for
  an already quasi-coherent ideal datum.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`,
  `blowupι`, `blowupFunctor`, `blowupNatTrans`, `blowupMap_preimage`, and
  `isPullback_blowupι`. In particular `blowupFunctor.map` uses the actual
  section restriction and `map_ideal`, and the map to V uses its affine Spec iso.
- `WeilConjectures.Blowup.Affine.Defs`: `AffineBlowup`, `AffineBlowup.toSpec`,
  `AffineBlowup.chart`, with `opensRange_chart`; these are the recorded
  affine-blowup and affine-chart declarations.
- `WeilConjectures.Blowup.Affine.ChartAlgebra`: `AffineBlowup.chartRing`,
  `homogeneousAwayEquivChart`, and its algebra-map compatibility. This is the
  exact dependency subalgebra, without a separate model.
- `WeilConjectures.Compactification.StrictTransformChartModel`:
  `AffineBlowup.chartRingι` and `chartRingιOfEq_toSpec`, the already defined
  canonical embedding obtained by Spec of the chart-ring equivalence followed
  by the recorded homogeneous Proj chart.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: `toModules`.

All stated proof dependencies are imported, using the recorded upstream modules:
`IntegralIdealGenericStalk`, `QuasiCoherentIdealZeroSetAffine`,
`QuasicoherentFiniteTypeAffine`, `Blowup.FiniteDegree.Algebra`,
`Blowup.Affine.Localization`, and `Sheaf.AlgebraicGeometry.PrincipalOpenDenseOfNonZeroDivisor`.
The gluing and morphism-gluing Mathlib matches use `Mathlib.AlgebraicGeometry.Gluing`;
other global-blowup proof dependencies are all in `WeilConjectures.Blowup.Gluing`.
The theorem docstring contains all nine proof steps with their DAG references.

Sources opened: `literature/stacks-project/divisors.tex`,
`lemma-blowing-up-affine` (0804) and `lemma-blow-up-integral-scheme` (02ND), and
`algebra.tex`, `lemma-blowup-domain` (052R). They identify these actual Proj,
localization-subalgebra and glued models.

Edge cases checked before writing: the empty scheme is excluded by integrality;
the empty affine open is excluded only where the node excludes it. A unit ideal
has U = T and is allowed. The zero ideal is excluded by hI. Individual zero
generators remain present and give empty charts. At r = 0 there is a single
possibly repeated generator; if it generates a nonzero ideal it cannot be zero.
An all-zero generating family cannot satisfy the generation hypothesis for the
nonzero affine ideal. Neither characteristic nor Noetherianity is restricted.
All objects and rings share the scheme universe u; there is no small test-object
quantifier or extra universe equality. `autoImplicit` is disabled.

Searches (2026-10-24):

- Required msearch LeanFinder query: "The blowup of an integral scheme along a
  nonzero finite type ideal has integral affine charts and dense center complement".
  Eight hits, including `IsIntegral`, `affine_isIntegral_iff`, integrality of
  normalization and open immersions. None includes this chart and density statement.
- Required msearch Loogle query: `"blowup", "IsDomain"`: zero hits.
- Required msearch grep query: `blowup|blowUp|Blowup` in Mathlib AlgebraicGeometry:
  zero hits.
- `rg` in `lean/WeilConjectures/Blowup` for integral blowups, chartRing and density
  found the construction APIs used above, but no theorem with all clauses.
  `grep -rn` of this item's id in `lean/WeilConjectures` found no declaration.
- `rg` in `lean/Sheaf` found `IntegralBlowupProjectiveGeometry`, which proves
  integrality/projectivity as a statement, not these chartwise density conclusions;
  the DNC and strict-transform chart modules specialize different centers.
- `dag/lean_names_upstream.json` was consulted for blowup/chart declarations;
  the new theorem name was searched in Mathlib, WeilConjectures and Sheaf with no hit.

No statement correction, disputed statement, new definition node, or dependency
repair is needed. The first compilation exposed two elaboration issues (the
unqualified finite-type universe inference and inference of the ambient scheme
for `toScheme`); use dot notation and explicitly supply `(X := T)` respectively.

## Second reading by Q26

A separate worker self-check reopened the node and the module, comparing each
hypothesis and clause as enumerated above. This is a self-check, not a claim of
an independent reviewer; the dispatcher's maintainer supplies independent review.
The read found that treating the affine comparison as a cartesian square is
sufficient because its vertical leg is the existing open immersion and its open
range is explicitly the inverse image of V. It also checked that every occurrence
of chart density refers to the whole chart spectrum, and that zero generators
are not omitted. No mathematical changes to the node were required.

Validation: `scompile.py Q26 lem-sfb-integral-blowup-chart-density` compiled both
its sandbox check and the final named module successfully, with no errors or
warnings. The only proof is the requested theorem's `sorry`.
