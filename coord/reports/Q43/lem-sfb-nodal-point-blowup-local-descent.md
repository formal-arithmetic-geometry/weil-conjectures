## Worker report

The delivery states `AlgebraicGeometry.DvrNodal.nodal_point_blowup_local_descent`
in `Sheaf.AlgebraicGeometry.NodalPointBlowupLocalDescent`. Its sole theorem proof
is `sorry`. There are no new notions or new nodes. The item statement, proof and proof dependencies are unchanged. The existing
reduced-point-ideal, extended-ideal and ordinary-double-point owners are cited, and
a new existing:true ownership node records the seven plain chart-data declarations
that the chart theorem module supplies.

Source read: Stacks `models.tex`, `example-blowup` (0CDC) and the full
`lemma-blowup-at-worst-nodal` (0CDE), especially the two-centre Cartesian diagram
and the final residue-field argument; `divisors.tex`'s flat blowup comparison is
represented by the published `WeilConjectures.Blowup.FlatBaseChange` interface.
The node already corrects the source's erroneous n>2 residual-singularity range:
n=3 has middle chart rs=π and is regular. No further statement correction is needed.
The prescribed CompactObject example is now withdrawn; its node points to the
upstream module. The new files follow the required module/public-section format.

Hypotheses, individually:

- `R R' : CommRingCat.{u}`, `[IsDomain R]`, `[IsDiscreteValuationRing R]`, and
  the corresponding instances for R' express the two DVRs. `π`, `hπ` say that π
  generates the maximal ideal. `K`, `[Field K]`, `[Algebra R K]`, `[IsFractionRing R K]`
  give the fraction field. The residue field need not be separately named: the
  special-fibre point is `IsLocalRing.closedPoint R`, with its canonical residue field.
- `φ`, `hφ`, `[IsLocalHom φ]`, `[Etale (Spec.map (CommRingCat.ofHom φ))]` are
  exactly the local injective étale extension. `hπ'` says φ(π) is a uniformizer.
- `f : X ⟶ Spec R`, `[Flat f]` express the flat family. Local finite presentation,
  quasi-compactness and quasi-separatedness together express the node's *finite*
  presentation. These are not extra geometric restrictions.
- `hgeneric` says the projection of the actual base change to Spec K is smooth.
- For every algebraically closed Ω and every geometric base map g, `hfibres`
  asserts reducedness and pure dimension one. Its pointwise clause tests closed
  z and failure of smoothness on any neighbourhood; the resulting
  `IsGeometricOrdinaryDoublePoint Ω (pullback f g) z` unfolds to the specified
  maximal-ideal-adic completion ring isomorphism with Ω[[a,b]]/(ab).
- `x`, `hx`, `hspecial`, `hnotregular` specify a reduced closed nonregular
  special-fibre point. Closedness in X is equivalent to closedness in the special
  fibre since that fibre is closed. No assumption that X is globally regular is made.
- `n`, `hn`, `o`, `ho` give n≥2 and the model origin, using `DvrNodal.model`
  and `DvrNodal.IsOrigin`. Its ring is the existing `strictNodalRing R' ((φ π)^n)`.
- `p`, `q`, their étale instances, `hover`, `u`, `hux`, `huo` give both pointed
  étale S-maps and their commutativity over Spec R, with the specified origins.

Conclusions, individually:

- `∃ V v, V.ι v = u` is the allowed open restriction of U. `hv` asserts that the
  remaining point is closed. Both `comap` equalities identify the two
  scheme-theoretic inverse-image ideals with `pointIdeal v hv`; they retain scheme
  structure and do not assert equality of any residue fields.
- `pPlus`, `qPlus` have precisely the two point-blowup domains and codomains.
  Each `IsPullback` says its comparison square is Cartesian, including the
  commutativity equation; with the blowup maps fixed, this determines the comparison
  map. `Etale pPlus ∧ Etale qPlus` is the top-map assertion. The quantified y clause
  says every point mapping to x lifts along pPlus.
- `Flat` and `LocallyOfFinitePresentation` of `(pointIdeal x hx).blowupMap ≫ f`
  give exactly the asserted properties of X⁺→S. The following geometric-fibre
  clause repeats precisely reducedness, purity and the closed nonsmooth-point
  completion condition, using the same existing ordinary-double-point definition.
- The displayed `IsIso (pullback.map ...)` is the map induced by the actual
  blowup on generic fibres, over the identity of Spec K. Thus the claimed
  generic-fibre isomorphism is canonical and respects its given map to X_K.
- `IsIso (blowupMap ∣_ support.compl)` is the isomorphism over X\{x}, since
  `pointIdeal x hx` is the vanishing ideal of exactly that singleton.
- `(n = 2 ∨ n = 3) → ...` asserts regularity of every point above x in both
  stopping cases separately, without a false residual point at exponent one.
- `4 ≤ n → ∃ xPlus, ...` gives a nonregular closed point over x and the
  quantified uniqueness clause for all other nonregular points above x.
  Its `W,w,a,c` give a common pointed étale neighbourhood, with c(w) satisfying
  `IsOrigin R' (φ π) (n-2)`. The final equation makes it a neighbourhood over S.
- The final regularity equivalence for points mapping away from x records that
  local regularity is unchanged there, hence no new nonregular points occur.

Dependency declarations read and reused:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`,
  uniformizers as maximal-ideal generators (the recorded match).
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- Mathlib morphism modules: `Flat`, `LocallyOfFinitePresentation`, `Smooth`, `Etale`;
  finite presentation also uses `QuasiCompact` and `QuasiSeparated`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.snd`, `pullback.map`; `IsPullback` is the square predicate.
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension` (componentwise,
  vacuous for the empty scheme).
- `Mathlib.RingTheory.AdicCompletion.Basic`, `Mathlib.RingTheory.MvPowerSeries.Basic`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `AdicCompletion`, `MvPowerSeries`,
  `IsAlgClosed`, as used by the existing ordinary-double-point definition.
- `Sheaf.AlgebraicGeometry.ProjectiveNodalTower`:
  `IsGeometricOrdinaryDoublePoint`; only this completion predicate is used, not
  its projectivity or connectedness predicates.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: the recorded scheme convention;
  pointwise statements use its underlying `IsRegularLocalRing`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `Sheaf.AlgebraicGeometry.DvrNodalChartBlowupCalculus`: the existing owner node
`def-sfb-dvr-nodal-chart-data` records `constant`, `coordinate`, `originIdeal`,
`model`, `projection`, `centre` and `IsOrigin`; the theorem node
`lem-sfb-dvr-nodal-chart-blowup-calculus` supplies `model_properties` and
`blowup_geometry` for the proof.
- `Sheaf.AlgebraicGeometry.SurfacePointBlowupData`: `SurfacePointBlowup.pointIdeal`,
  whose data are literally `vanishingIdeal ⟨{p},hp⟩`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `IdealSheafData.comap`.
- Proof-only imports include the flat comparison, complement, étale reducedness,
  closed-point field criterion, binomial fibres, finite-residue closedness,
  source locality, étale discrete separable fibres, finite-limit and surjective
  base-change tools. The three proof nodes with no Lean record/match are
  lem-sfb-etale-stalk-invariants, lem-sfb-monomial-local-completion and
  lem-sfb-space-nodal-chart-locality; they do not introduce notions in this signature.

Searches actually run:

- msearch leanfinder, “Etale descent of a singular point blowup of a nodal curve
  over a discrete valuation ring”: eight standard étale/local smoothness results;
  no statement of the point-blowup descent theorem.
- msearch loogle, `AlgebraicGeometry.DvrNodal, blowup`: zero results, unknown
  identifier for that namespace in the search index.
- msearch grep, `nodal|Nodal|blowup`, Mathlib/AlgebraicGeometry: zero hits.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `nodal.*blowup|blowup.*nodal`: the chart calculation, regularization and
  symmetric blowup appear, but none states this local descent theorem.
- `rg` for point-ideal declarations found SurfacePointBlowup.pointIdeal; searches
  of DAG module references found its existing owner, which is reused.
- DAG searches for `IdealSheafData.comap` found def-nagata-extended-ideal.
  `dag/lean_names_upstream.json` had no new-theorem-name conflict.

Edge cases checked: n=2 gives middle equation rs=1; n=3 gives rs=π; n=4
retains the ordinary n=2 singularity. Unequal finite separable residue fields
at u and x are allowed; coverage does not identify them. Empty/disconnected
geometric fibres satisfy precisely the stated conditions without ConnectedSpace.
The marked point forces only the relevant special fibre to be nonempty. No
completeness, excellence, perfectness or characteristic-two exclusion is present.
All type/universe variables are explicitly bound and all geometric test fields
are in the same scheme universe, as in the recorded geometric-fibre conventions.

## Second reading by Q43

The worker reread the completed file against every hypothesis and clause above;
no independent second agent was started, as the dispatcher brief forbids it.
The maintainer supplies the independent mathematical review. On rereading, checked
that finite presentation retains both compactness conditions, that the two extended
centres are equalities of ideal sheaves, that exceptional coverage quantifies over
all points, and that the two stopping exponents are both present. The residual
neighbourhood is over S and uses precisely n-2. The completion predicate has no
connectedness requirement. The dependency repair leaves all mathematical
signatures and data intact. Compiler-driven repairs only fix identifier syntax,
make the geometric-fibre carrier coercions explicit, and supply the identity
commutativity equality for the canonical generic-fibre map.

Validation: scompile compiled both modules separately in dependency order, including
their actual library module names, with no errors or warnings. The main file took
3.9 s as sandbox and 3.2 s as library. The dependency sandbox took 2.6 s.

## New nodes

`def-sfb-dvr-nodal-chart-data` is an existing:true ownership node, not a new Lean module. Its statement packages the arithmetic nodal quotient, coordinate and constant classes, origin ideal, Spec model and projection, centre ideal sheaf, and origin predicate. Searches found no Mathlib or other DAG owner; the exact declarations are already in `Sheaf.AlgebraicGeometry.DvrNodalChartBlowupCalculus`, so the delivery records them without copying.

Repair note: the source-locality dependency module and its node-file change were removed as requested. The theorem remains in `proof_deps`; proof-only imports that are not needed to elaborate this statement were removed, while statement-facing imports remain.
