## Worker report

The delivery states lem-sfb-flat-pullback-blowup-chart-restrictions in
Sheaf.AlgebraicGeometry.FlatPullbackBlowupChartRestrictions. There are three named
sorry theorems, all attached to this node: blowup_flat_chart_restrictions (steps 1–4),
blowup_flat_fiber_residue (step 5), and etale_blowup_reduced_point_neighbourhood
(step 6). Definitions contain real data. No mathematical statement was corrected,
no dependency record was replaced, and no independent new notion was introduced.

Hypotheses and clauses, matched to Lean:

- Schemes X,Y and the flat morphism g are `{X Y : Scheme.{u}} (g : Y ⟶ X) [Flat g]`.
  The common universe is the existing Scheme API's universe and is arbitrary.
- The quasi-coherent ideal is `I : X.IdealSheafData`. Its actual sheaf of modules is
  `I.toModules`; finite type together with quasi-coherence is the recorded predicate
  `Scheme.Modules.IsQuasiCoherentFiniteType I.toModules`, the hypothesis hI on each
  of the three theorems. It is not replaced by coherence or a Noetherian condition.
- The extended ideal J is always `I.comap g`, the recorded kernel-of-pullback
  construction. Thus its affine ideal at V is the actual ideal of the pulled-back
  centre, not an independently chosen ideal. `ideal_comap_appLE` in the public
  FlatBaseChange imports identifies it with `(I.ideal U).map (g.appLE ...).hom`.
- Ordinary blowups are `I.blowup` and `(I.comap g).blowup`. The map used throughout
  is exactly `I.blowupFlatBaseChange g`. Upstream places the old blowup in the FIRST
  pullback factor and Y in the second; the source's displayed product has the opposite
  order. The projections in this delivery follow the upstream order. This is the same
  comparison after the canonical symmetry, not a change of mathematical assertion.
- The affine opens are `U : X.affineOpens`, `V : Y.affineOpens`, and inclusion
  `h : V.1 ≤ g ⁻¹ᵁ U.1`. Their rings are Γ(X,U.1), Γ(Y,V.1); the map φ is exactly
  `(g.appLE U.1 V.1 h).hom`. `BlowupChartBaseChange` installs its `toAlgebra` with
  letI; this installs an instance only, not a hidden proposition or a chosen map.
- All generators are included by `∀ a, ∀ ha : a ∈ I.ideal U`. The membership hb
  records φ(a) in J(V). `fractionChartι` is constructed from the existing
  homogeneousAwayEquivChart, AffineBlowup.chart, and I.blowupι U, so it is the
  actual standard open chart `Spec A[I/a]`, not an arbitrary affine embedding.
- The existential `e` is precisely the B-algebra equivalence
  `B ⊗[A] chartRing I(U) a ≃ₐ[B] chartRing J(V) φ(a)`.
  Its first conjunct specifies its value on EVERY pure tensor b⊗z in the ambient
  localization by `algebraMap B _ b * Localization.awayMap φ a z`. Setting z=c/a
  is exactly bφ(c)/φ(a); it also specifies higher fractions and coefficients.
  No unconstrained comparison is substituted for this formula.
- The next equality identifies the old-blowup projection of the specified global
  comparison on this chart with `Spec.map (e ∘ includeRight) ≫ fractionChartι`.
  The following equality gives its structural map to Y as `Spec.map (algebraMap B _)
  ≫ V.2.fromSpec`. As e is a B-algebra equivalence it respects B structurally.
- The `Set.range` equality says exactly that, over V, the inverse image of the
  old a-chart under the specified comparison is the new φ(a)-chart. Intersection
  with the inverse image of V is necessary because V is any affine open inside
  g⁻¹U, not the whole inverse image. Both chart maps are the canonical open
  immersions; the ring equivalence and previous diagram supply the scheme assertion.
- `Ideal.map e.toRingHom ((I.ideal U).map (algebraMap A _)) =
  ((I.comap g).ideal V).map (algebraMap B _)` identifies the centre ideals.
- For EVERY c : I(U), `chartGenerator I(U) a c` is literally c/a in chartRing.
  The final conjunct gives an equivalence of the two localizations away from
  `1 ⊗ c/a` and `e (1 ⊗ c/a)` with the formula z/u^n ↦ e(z)/e(u)^n.
  The first pure-tensor formula identifies e(u) with φ(c)/φ(a), so the target
  localization is exactly the stated overlap ring. Restriction agreement comes
  from the preceding global chart diagram; localizing that diagram is its overlap
  restriction. This covers any a'∈I, including zero and repeated generators.
- For y:Y, `blowup_flat_fiber_residue` gives an actual scheme isomorphism from
  `(I.comap g).blowupMap.fiber y` to
  `pullback (I.blowupMap.fiberToSpecResidueField (g y))
  (Spec.map (g.residueFieldMap y))`. This is precisely the displayed iterated
  fibre product with κ(x)→κ(y), with x defined as g(y). Its two projection equations
  characterize the canonical map: projection to the old blowup is the fibre
  inclusion followed by bc_g and its first projection; projection to Spec κ(y)
  is the new fibre's structure morphism. Pulling the chart equation back gives
  chart compatibility. Neither residue field is replaced by the other.
- For the last clause, `[Etale g]`, `hx : IsClosed {g y}`, and
  `hcentre : I = (X.fromSpecResidueField (g y)).ker` are exactly the additional
  assumptions. The conclusion gives V open, y∈V, and a closed immersion
  `i : Spec (Y.residueField y) ⟶ V.toScheme` with
  `i ≫ V.ι = Y.fromSpecResidueField y`. Thus it is the actual reduced point y,
  not a thickening or an arbitrary residue-field point. Equality
  `(I.comap g).comap V.ι = i.ker` is the equality of ideal sheaves on V.
  Applying the already universally stated flat chart comparison over this
  neighbourhood gives the asserted comparison for Bl_y V. Etale flatness and
  restriction are existing instances; no additional hypothesis is required.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Morphisms.Flat: AlgebraicGeometry.Flat and its affine
  and stalkwise characterizations; Mathlib.AlgebraicGeometry.Morphisms.Etale:
  AlgebraicGeometry.Etale; Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion:
  AlgebraicGeometry.IsClosedImmersion.
- Sheaf.AlgebraicGeometry.CoherentFiniteType:
  Scheme.Modules.IsQuasiCoherentFiniteType; it retains the recorded conjunction
  of SheafOfModules.IsQuasicoherent and IsFiniteType.
- Mathlib.AlgebraicGeometry.IdealSheaf.Functorial: Scheme.IdealSheafData.comap;
  Mathlib.AlgebraicGeometry.IdealSheaf.Basic: Scheme.Hom.ker.
- WeilConjectures.Blowup.Gluing: Scheme.IdealSheafData.blowup, blowupMap, blowupι;
  WeilConjectures.Blowup.FlatBaseChange: reesPullbackData, reesPullbackMap,
  blowupFlatBaseChange, blowupFlatBaseChangeIso. The two dependencies without lean
  records have closed upstream audits naming these exact declarations; used directly.
- WeilConjectures.Blowup.Affine.ChartAlgebra: AffineBlowup.chartRing,
  homogeneousAwayToChart, its injectivity/surjectivity/formula, and
  homogeneousAwayEquivChart. Their full definitions allow zero divisors.
- Mathlib.LinearAlgebra.TensorProduct.Defs: TensorProduct; its pure tensor
  notation and Mathlib's Algebra.TensorProduct.includeRight specify the structural
  ring map. Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback,
  pullback.fst and pullback.snd.
- Mathlib.AlgebraicGeometry.ResidueField: Scheme.residueField,
  Scheme.Hom.residueFieldMap, Scheme.fromSpecResidueField;
  Mathlib.AlgebraicGeometry.Fiber: Scheme.Hom.fiber, fiberι,
  fiberToSpecResidueField.
- The proof-only imports preserve the stated proof plan:
  Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension,
  Sheaf.RingTheory.HomogeneousLocalizationScalarExtension,
  WeilConjectures.Blowup.Affine.Principalization,
  WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization,
  WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage,
  WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints.
  The affine ideal formula proof dependency is publicly supplied by FlatBaseChange's
  import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine.

Sources read: Stacks divisors.tex lemma-blowing-up-affine (0804) and
lemma-flat-base-change-blowing-up (0805), and morphisms.tex
lemma-etale-over-field (02GL), particularly part (2). The final shrinking follows
by removing the other components of the closed discrete fibre; no finiteness of
that fibre is assumed.

Edge cases checked: empty schemes and opens; I=0 and I=unit; a=0 or nilpotent;
a a zero divisor; zero chart rings; a'=a, a'=0 and empty overlaps; identity base
change; finite or infinite etale fibres; nontrivial κ(x)→κ(y). There is no
nonzero-denominator assumption, no nonempty-fibre assumption before selecting y,
no finiteness assumption on the etale fibre, and no residue-field equality.
The closedness hypothesis on x is retained for the reduced-centre shrinking.

Searches actually run through msearch.py (group N9, this item):

- LeanFinder: “Flat base change of blowup standard charts tensor ring fraction
  generators overlap localizations and exceptional fibres”. Eight results on
  standard smoothness/base change and standard open immersions; no exact match.
- Loogle: “AffineBlowup.chartRing, blowupFlatBaseChange”. Zero hits; chartRing
  is unknown to the public Loogle index. Recorded as an index limitation.
- Mathlib grep: `(blowupFlatBaseChange|chartRing)` under AlgebraicGeometry.
  Zero hits. Upstream supplies these constructions.
- LeanSearch: “Flat base change of blowup charts identifies tensor fraction
  coordinates overlap localizations and exceptional fibres”. Eight partial flatness
  and module-localization results, no exact theorem.
- rg of lean/WeilConjectures and lean/Sheaf for this item id, chartRing with
  baseChange/BaseChange, and blowupFlatBaseChange. This found FlatBaseChange,
  ChartAlgebra and the alternative StrictTransformChart API, plus existing
  consumers; none states the complete node. The strict-transform API divides out
  torsion for arbitrary base changes, so it is not the present flat comparison.
- rg of both library roots and dag/lean_names_upstream.json for each proposed new
  name found no existing declaration. Helpers use chartRing and homogeneous charts
  directly and introduce no second chart-ring construction.

Server validation: scompile.py checked the sandbox module and its final module
name independently, both clean (11.0 s and 11.6 s). All three theorem proofs are
exactly sorry; every universe and variable is explicitly bound. No statement fault
or STATEMENT-DISPUTED issue remains.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
