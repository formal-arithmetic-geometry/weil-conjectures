## Worker report

The module `Sheaf.AlgebraicGeometry.CospanCompatibleFSCharts` states
`AlgebraicGeometry.EtaleLogHom.exists_cospan_compatible_fs_charts` with `sorry`.
Nothing is proved. All helper structures and definitions contain actual data.
The natural-language statement and accepted stage-1 proof are unchanged.

The inherited BLOCKED ending concerned a stage-1 unchanged-item rejection.
The current node is split and reviewed, has no Lean record, and occurs in the
stage-2 queue. The stage handoff in brief-stage2 section 0 explicitly permits this
stage-2 attachment. There is no repair note for the item.

Clause-by-clause correspondence:

- The locally Noetherian fs log schemes are `X Y Z : FineSaturatedLogScheme`.
  This existing structure includes `scheme`, `locallyNoetherian`, `logStructure`
  and `fineSaturated`. The arbitrary actual log morphisms are the binders
  `f : EtaleLogHom X Z` and `g : EtaleLogHom Y Z`.
- The ordinary scheme product is `pullback f.base g.base`, using the recorded
  Mathlib fibre product, rather than an fs log product. Its additional local
  Noetherian hypothesis is `[IsLocallyNoetherian (pullback f.base g.base)]`.
- The existential `I : Type u` and `C : I → FSLogCospanNeighbourhood f g`
  give the family. Its first conclusion explicitly says that every underlying
  point `w` has an inverse image in some `(C a).H`. No nonemptiness hypothesis is
  imposed on either the index set or any scheme.
- The helper `FSLogCospanChart` uses the already defined squares
  `left : FSLogChart f` and `right : FSLogChart g`. Their `W` objects are etale
  over `Z`; their `V` objects are etale over `X` and `Y`.
  `commonBase` identifies the same target neighbourhood. `commonP`,
  `commonMonoid`, and `commonChart` identify its actual monoid, monoid structure,
  and chart, not an unrelated abstract isomorphism. `affineBase`, `affineLeft`,
  `affineRight` say that these three neighbourhoods are affine.
- The fields `etaleLeft` and `etaleRight` assert that the canonical refinements
  into `X ×_Z Z_a` and `Y ×_Z Z_a` are etale. They are the `pullback.lift` of the
  actual source-neighbourhood and chart-square maps. The right target is the
  same `Z_a` by `commonBase`.
- The existing `FSLogChart` supplies `fineP`, `fineQ`, `chartY`, `chartX`,
  `chartY_isChart`, `chartX_isChart` and `g`. Its chart conditions use the
  ambient log sheaves on etale neighbourhoods, exactly the restricted log
  structures. The two chart-square `g` fields are the node's `h_a` and `k_a`.
  `chart_compatibility` is equality with `f.sectionMap` and `g.sectionMap`,
  respectively. Thus these are the actual log maps on chart sections.
  Their unit behavior is that of the given log morphisms: the unit condition
  makes the structural map an isomorphism on units, and `EtaleLogHom.compatibility`
  forces their images to be the scheme pullbacks of the corresponding units.
  `FSLogChart.square` is the consequent canonical square of monoid-ring spectra.
  Neither `IsSmoothChart` nor `IsEtaleChart` is assumed.
- `FSLogCospanChart.rightMap` transports the second square's map to the identical
  target using `eqToHom` of `commonBase`. It introduces no arbitrary map.
  `inclusion` lands in `pullback left.map rightMap`, the stated
  `X_a ×_{Z_a} Y_a`, and `openImmersion` says that it is an open immersion.
  `affine : IsAffine H` makes it an affine open. An affine scheme is canonically
  the spectrum of its actual ring `Γ(H, ⊤)`; `noetherian` says that this ring is
  Noetherian. This is the node's presentation `H_a = Spec A_a` up to its
  canonical affine-scheme identification, not an extra chosen log structure.
- `toBase` is the map `H_a → W`, and `fst_eq` and `snd_eq` normalize both of its
  projections to the chart-product projections. These two equations determine
  the canonical map uniquely by the fibre-product universal property.
  `etale : Etale toBase` is the etale clause for `H_a → W`.
- `pushoutCongruence` is literally `conGen` of the pairs
  `(left.g p, 1)` and `(1, right.g (cast commonP p))` on `left.Q × right.Q`.
  `monoidPushout` is its actual `Con.Quotient`, with the inherited commutative
  monoid structure. Multiplicative `1` here is additive `0` in the node; product
  is the finite monoid direct sum. It is not saturated or integralized.
- The fourth conjunct supplies `φ` from that quotient to the actual section
  ring of `H_a`. Its equation for every `q,r` fixes its value on every quotient
  representative as the product of the two structural chart images pulled
  back along `inclusion` and the two product projections. Consequently this
  is the induced structural homomorphism, not an arbitrary map of those types.
- The second conjunct quantifies over every affine open `U` of `W`. It gives
  `n : ℕ`, `a : Fin n → I`, and equality of the union of the entire images of
  the chosen `H_(a j)` with `U`. Thus each selected neighbourhood lands inside
  `U`, and finitely many of the same chart neighbourhoods cover it.
- The third conjunct is
  `Presieve.singleton (Sigma.desc (fun a ↦ (C a).toBase)) ∈
  Scheme.fpqcPrecoverage W`. The source of `Sigma.desc` is the actual scheme
  coproduct of the `H_a`, and its coprojection equations fix the single map.
  This is the node's singleton fpqc conclusion using the recorded definition.
  It does not assert that the infinite coproduct map is quasi-compact.
- The final conjunct imposes the strict choices on the same family. On each
  strict leg its source monoid equals its target monoid, their monoid
  structures agree, and its homomorphism is heterogeneously equal to
  `MonoidHom.id`. The existing `chart_compatibility` then says exactly that its
  source chart is the composite of the target chart and the actual section
  pullback. Since the common target chart is identified by the preceding
  fields, these are `Q_a = P_a, h_a = id` and `R_a = P_a, k_a = id`.
  Both implications are simultaneous, so both strict legs are retained.

The helpers above package data of this theorem; no independent mathematical
notion or postponed helper theorem has been introduced. The module's only
`sorry` is the named theorem, whose docstring gives all ten proof steps.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `FineSaturatedLogScheme`, `EtaleLogStructure.IsChart`, `EtaleLogHom`, and its
  section and structural compatibility fields (def-trf-fs-log-blowup).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  `pullback.lift` (def-pc-fibre-product).
- `Mathlib.AlgebraicGeometry.Sites.Etale` and
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`:
  `Scheme.smallEtaleTopology`, `Scheme.Etale`, `Etale`
  (def-weil-pbc-etale-site and def-weil-etale-morphism).
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`:
  `Scheme.fpqcPrecoverage` (def-weil-pbc-fpqc-covering). Its quasi-compact cover
  condition permits finite affine opens in an infinite coproduct.
- `Sheaf.AlgebraicGeometry.FSStrictLogMorphism`:
  `EtaleLogHom.IsStrict`, normalized by `CharacteristicRelation`
  (def-per-strict-log-morphism).
- `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`: `FSLogChart`, its two charts and
  their compatibility (def-per-fs-log-smooth-etale). This already landed node
  is added to `stmt_deps`, as permitted by brief-stage2 section 5, to cite the
  shared square interface rather than define another compatible log square.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
  `Mathlib.AlgebraicGeometry.Limits`: scheme coproduct existence.

The stated proof providers are imported privately:
`FsFaceSharpening`, `FineLogStalkChartSpreading`, `AssociatedLogUniversalStalks`,
and Mathlib's EtalePoint, AffineScheme, Pullbacks, UniversallyOpen,
QuasiSeparated, and Flat modules. The recorded source modules of the remaining
Mathlib proof dependencies are also public statement imports where appropriate.
Two proof-only nodes have no recorded Lean declaration or Mathlib match:
`lem-trf-chart-face-localization-logification` and
`lem-trf-finite-monoid-stalk-data-spreading`; no missing proof-only import is
invented for them. They are not needed to type this statement and do not justify
writing a duplicate statement or proof here.

Source and edge cases:

Read ILO VI 1.1, printed p. 69 (PDF p. 75), and X proof of Theorem 3.5,
Step 6, printed p. 164 (PDF p. 170). The former explicitly uses etale-local fs
charts and assumes locally Noetherian schemes throughout. The latter has the
common chart and pushout `R_i` in its special Zariski situation. The DAG
correctly labels the arbitrary-morphism refinement as agent supplied; the Lean
docstring preserves its finite-unit-coordinate argument and does not misquote
it as a theorem of ILO X.

Checked empty `W` (empty `I`, `n = 0`, empty coproduct), empty affine opens,
trivial log structures and monoids, noninjective chart homomorphisms, torsion
units, infinite covers, either strict leg and both strict legs. No log smooth,
Kummer, log regular, or finite-type hypothesis on `f` or `g` was added.
`I : Type u` permits a small covering family, consistent with the small etale
site and the scheme coproduct universe; it does not constrain all possible
families to be small. Chart monoids and schemes use the existing framework's
universe `u`. `autoImplicit` is false.

Searches for an existing statement:

- msearch LeanFinder: "Compatible fine saturated charts for a cospan of
  logarithmic scheme morphisms with a common target". Eight hits, all on
  ordinary scheme approximation or pullback construction; no log cospan chart
  existence theorem.
- msearch Loogle: `"LogStructure"`. Zero hits.
- msearch grep in Mathlib/AlgebraicGeometry:
  `LogStructure|LogScheme|FineSaturated`. Zero hits.
- Local ripgrep in `lean/WeilConjectures`:
  `lem-per-cospan-compatible-fs-charts|FineSaturatedLog|FSCospan`. Zero hits.
- Local ripgrep in `lean/Sheaf/AlgebraicGeometry` log and chart modules:
  `CompatibleChart|compatibleChart|LogChart|ChartSquare|Cospan|cospan`.
  Found the shared `FSLogChart` and specialized log-smooth/strict chart
  statements, but no assertion of this cospan cover. Those existing squares
  are reused in this delivery.
- Mathlib monoid-category and congruence source search: no dedicated
  commutative-monoid pushout implementation in the monoid-category modules;
  `conGen`, `Con.Quotient`, `Con.mk'`, and the quotient `CommMonoid` instance
  give exactly the quotient explicitly required by this item. The general
  quotient/congruence notions are reused, not redefined.

Validation: `scompile.py` compiled the file cleanly in sandbox mode and its
actual library module mode. The first probe exposed ambiguous coercions in
scheme-point binders for `pullback`; these were repaired by writing the
explicit point-sort coercions `↥(pullback ...)`. No warning remains. The final
imports and node/report packet are checked again by `deliver2.py --no-push`.

No statement fault, correction, or STATEMENT-DISPUTED flag.

## Second reading by Q135

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
