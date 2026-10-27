## Worker report

Item: lem-sfb-point-blowup-local-chart-package. The delivery states
`AlgebraicGeometry.PointBlowupLocal.point_blowup_local_chart_package` in
`Sheaf.AlgebraicGeometry.PointBlowupLocalChartPackage`. Its only postponed proof is
that theorem. All nine auxiliary definitions have complete bodies; they spell out
maps or groups of clauses of this same package, rather than introduce an independent
mathematical notion. No node statement or dependency record is changed.

Source read: literature/stacks-project/divisors.tex, Tags 0804 and 0805
(lemma-blowing-up-affine and lemma-flat-base-change-blowing-up), and
resolve.tex, Tag 0AGS, first proof paragraph. The complete nine-step accepted DAG
proof, with its dependency IDs, is reproduced in the theorem docstring. No proof
is supplied at stage 2.

Hypotheses and clauses, in order:

- A regular scheme T is `(T : Scheme.{u}) (hregular : IsRegularScheme T)`. This uses
  the dependency's locally Noetherian AND stalkwise regular definition. The bound
  is `hdim : topologicalKrullDim T ≤ 2`. The point and its closedness are
  `(x : T) (hx : IsClosed ({x} : Set T))`. No global Noetherianity, integrality,
  connectedness, field, excellence or nonempty-exceptional-fibre hypothesis is added.
- The reduced centre is exactly `Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩`.
  Its existing `.blowup` and `.blowupMap` are W and b; no second blowup is defined.
- `∃ (V : T.affineOpens) (hxV : x ∈ V.1)` is the affine neighbourhood.
  Its existing `V.2.isoSpec` identifies it with Spec R for `R = Γ(T,V.1)`.
  `IsNoetherianRing Γ(T,V.1) ∧ IsRegularRing Γ(T,V.1)` are the two ring clauses.
- The prime p is `(V.2.primeIdealOf ⟨x,hxV⟩).asIdeal`; the explicit
  `.IsMaximal` clause is maximality. A is literally `T.presheaf.stalk x`, rather
  than an arbitrary isomorphic ring. The existential equivalence from
  `Localization.AtPrime p` to this stalk must satisfy
  `e.toRingHom.comp (algebraMap _ _) = (T.presheaf.germ V.1 x hxV).hom`.
  Thus it identifies the actual germ map, not just the ring carriers.
  `Ideal.map germ p = IsLocalRing.maximalIdeal A` says m = pA.
- The restricted morphism is the actual `b ∣_ V.1 : (b ⁻¹ᵁ V.1).toScheme ⟶ V.1`.
  `IsProper (b ∣_ V.1)` is its properness.
- `IsRegularLocalRing A ∧ IsDomain A` and the explicit disjunction
  `ringKrullDim A = 0 ∨ ringKrullDim A = 1 ∨ ringKrullDim A = 2` give regular
  locality, domainhood and the dimension alternatives. Only A, not R, is a domain.
- `PointBlowupLocal.model` is exactly `(b⁻¹V) ×_V Spec A`, with the canonical
  `V.1.fromSpecStalkOfMem x hxV`; `projection` and `toBlowup` are its two
  structural projections (the latter composed with the open inclusion).
- `Comparisons` names I, A, J = I.comap (T.fromSpecStalk x), and m by definitional
  let-bindings in its BODY. The theorem signature itself has no let-binders.
  It supplies `e : model ... ≅ pullback I.blowupMap (T.fromSpecStalk x)` with
  equations fixing BOTH projections. These equations specify the canonical
  associativity comparison, without replacing it by an arbitrary isomorphism.
- `J = (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))).ker` identifies the
  pulled-back centre with the reduced closed point of Spec A.
- The global/affine comparison `ea : J.blowup ≅ AffineBlowup m` lies over Spec A.
  For `S = Spec A`, `hm` states that the centre on the singleton top affine chart,
  transported by `(Scheme.ΓSpecIso A).hom.hom`, is m. The equation
  `ea.inv = AffineBlowup.hom (Scheme.ΓSpecIso A).hom.hom hm ≫ J.blowupι ⟨⊤,...⟩`
  fixes ea to the comparison obtained by the one-element affine cover. It does
  not substitute a merely existential over-base isomorphism for this comparison.
- The isomorphism Z → AffineBlowup m is SPECIFIED as
  `e ≪≫ (I.blowupFlatBaseChangeIso (T.fromSpecStalk x)).symm ≪≫ ea`.
  The middle arrow is the published canonical flat blowup comparison. In this
  version of the live source its target puts the blowup first and Spec A second,
  matching our product order. The final composite's structural equation states
  that its pullback of coefficients is the same as `projection`.
  `AffineBlowup m` is definitionally `Proj (reesGrading m)`.
- `ef` identifies the pullback of `projection` along `Spec(A → A/m)` with
  `I.blowupMap.fiber x`. The equations for `.fiberι` and
  `.fiberToSpecResidueField` fix both projections, hence the canonical scheme
  fibre identification, including its residue field and scheme structure.
- If `ringKrullDim A = 0`, `m = ⊥ ∧ IsEmpty (model ...)` states both conclusions.
  If it is 1, `IsIso (projection ...)` is the structural-map isomorphism.
- If it is 2, `TwoCharts A` supplies s,t belonging to m, `m = Ideal.span {s,t}`,
  `s ≠ 0`, `t ≠ 0`, and the dependency's
  `RingTheory.Sequence.IsRegular A [s,t]`.
- `TwoCharts` supplies opens Us,Ut of the affine Rees model and isomorphisms
  `es : Spec (AffineBlowup.chartRing m s) ≅ Us.toScheme`, and similarly et.
  `Us ⊔ Ut = ⊤` is the cover. The equations `es.hom ≫ Us.ι = ratioChart m s hs`
  and its t version identify the actual standard charts, using
  `homogeneousAwayEquivChart` and `AffineBlowup.chart`, rather than arbitrary
  opens having isomorphic rings. The two structural equations make these charts
  A-schemes with their natural coefficient maps.
- The explicit isomorphism Z ≅ AffineBlowup m just specified transports these
  opens, affine isomorphisms and structure maps to Z. Thus the chart clause on
  the named affine Rees model is the chart clause on Z under the displayed
  identification in the node. It neither changes Z nor assumes the chart package.
- `chartSections Us es` is the natural section-ring identification obtained from
  `Us.topIso`, `es.hom.appTop` and `ΓSpecIso`. The equations on rs and rt identify
  them with the actual fractions `chartFraction s 1 t` and `chartFraction t 1 s`
  in A_s and A_t. The two equations `Us ⊓ Ut = ...basicOpen rs` and its rt version
  are precisely the two basic-open descriptions of the intersection.
- The map ψ has domain `Γ(AffineBlowup m,Us ⊓ Ut)` and codomain
  `Localization.Away (s*t)`. Its first equation fixes its values on all coefficients
  a ∈ A, so it is an A-algebra map for the structural A-algebra on the section ring;
  this spelling avoids choosing a competing algebra instance. Its next two equations
  identify the composites with the actual presheaf restrictions from Us and Ut.
  The right-hand maps `leftInclusion` and `rightInclusion` are the standard
  `IsLocalization.Away.awayToAwayRight s t` and `awayToAwayLeft t s`, composed
  with the subalgebra inclusions into A_s and A_t, respectively.
- The final universal equation on every global section z is exactly equality of
  its two chart values in A_st. Transport by the specified Z-isomorphism gives
  the assertion for every section of Z.

Dependency declarations used (all recorded interfaces read in the local live source):

- def-weil-regular-scheme: Sheaf.AlgebraicGeometry.IsRegularScheme,
  `AlgebraicGeometry.IsRegularScheme`; the existing Mathlib ring predicates
  `IsRegularLocalRing` and `IsRegularRing` supply its ring clauses.
- def-kun-topological-krull-dimension: Mathlib.Topology.KrullDimension,
  `topologicalKrullDim`.
- def-nagata-global-blowup: WeilConjectures.Blowup.Gluing,
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup`, `.blowupMap`, `.blowupι`.
- def-weil-pbc-noetherian-ring: Mathlib.RingTheory.Noetherian.Defs,
  `IsNoetherianRing` (Noetherian as a module over itself).
- def-weil-pbc-localization-at-prime: Mathlib.RingTheory.Localization.AtPrime.Basic,
  `Localization.AtPrime`, with `IsLocalRing.maximalIdeal` and `.residue` for A.
- def-weil-proper-morphism: Mathlib.AlgebraicGeometry.Morphisms.Proper,
  `AlgebraicGeometry.IsProper`.
- def-weil-pbc-krull-dimension-ring: Mathlib.RingTheory.KrullDimension.Basic,
  `ringKrullDim`.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`.
- def-nagata-affine-blowup: WeilConjectures.Blowup.Affine.Defs,
  `AlgebraicGeometry.AffineBlowup`, `.toSpec`, `.chart`.
- def-nagata-blowup-flat-base-change-map: its closed slopmaster2 audit records
  WeilConjectures.Blowup.FlatBaseChange,
  `AlgebraicGeometry.Scheme.IdealSheafData.blowupFlatBaseChange`; this is exactly
  the map used by `.blowupFlatBaseChangeIso`. Although the node has no `lean`
  field, the closed audit is usable as permitted by brief-stage2 §0. No dependency
  repair or substitute construction is needed.
- def-weil-pbc-regular-sequence: Mathlib.RingTheory.Regular.RegularSequence,
  `RingTheory.Sequence.IsRegular`.
- def-nagata-blowup-chart-ring: WeilConjectures.Blowup.Affine.ChartAlgebra,
  `AlgebraicGeometry.AffineBlowup.chartRing`, `.chartFraction`,
  `.homogeneousAwayEquivChart`.
- def-weil-ring-localization-away: Mathlib.GroupTheory.MonoidLocalization.Away,
  `Localization.Away`, together with the ring maps of
  Mathlib.RingTheory.Localization.Away.Basic (public through ChartAlgebra).
- def-weil-pbc-module-stalk: WeilConjectures.Topology.PresheafModuleStalkFunctor,
  `PresheafOfModules.moduleStalkFunctor` and its underlying Mathlib stalk carrier.
  The ring stalk and germ used here are the underlying `TopCat.Presheaf.stalk`
  and `TopCat.Presheaf.germ`, not a replacement definition.

All stated proof-dependency modules are imported. Mathlib-match proof inputs use
AffineScheme, OpenImmersion, Scheme, Properties, ResidueField,
ProjectiveSpectrum.Topology and Spectrum.Prime.Topology. The other proof imports
are BlowupReesSymmetricPresentation, Affine.Proper, RegularLocalRing.Defs,
RegularLocalGeneratorsRegularSequence, FiniteDegree.Algebra,
GradedAlgebra.HomogeneousLocalization and ProjectiveSpectrum.Basic. The explicit
canonical stalk-flatness interface is public because it supplies the instance
needed to write the canonical comparison in the proposition.

Edge cases checked before writing:

- Empty T has no x, so the universally quantified theorem is vacuous without an
  artificial Nonempty assumption.
- T = Spec k and x its point: A = k, dimension zero, m = 0 and the blowup is empty.
  The fibre comparison is an empty-scheme comparison; no nonempty-fibre assumption
  from the parent regular-functions theorem was incorrectly imported here.
- A discrete valuation ring: dimension one, blowing up its principal nonzerodivisor
  maximal ideal gives an isomorphism over Spec A.
- A = k[s,t]_(s,t), or Z_(p)[t]_(p,t): the two chart rings are A[t/s] and A[s/t],
  and the overlap is the basic open inverting the opposite ratio. Both natural
  inclusions land in A_st and agree on restriction of a section.
- Disconnected or non-quasi-compact regular T is allowed; only a neighbourhood
  of x is chosen Noetherian. R is not required to be a domain.
- The universe u is arbitrary. No relation between unrelated universes, no
  restricted characteristic, and no equal-characteristic hypothesis is imposed.

Searches for an existing full statement or construction:

- msearch.py leanfinder: “Blowup of a closed point on a regular scheme of dimension
  at most two local ring two affine charts overlap localization”. Eight hits,
  including IsAffineOpen.isLocalization_stalk and fromSpecStalk_closedPoint;
  none states this package.
- msearch.py loogle: `AlgebraicGeometry.AffineBlowup, Localization.Away`.
  Zero hits; Loogle reports its index does not know the project-only
  AlgebraicGeometry.AffineBlowup identifier.
- msearch.py grep: `point.*[Bb]lowup|[Bb]lowup.*[Ll]ocal|chartRing`, Mathlib
  AlgebraicGeometry. Zero hits for the full package.
- rg in lean/WeilConjectures and lean/Sheaf for point/blowup/local combinations:
  found the existing affine blowup and chart algebra API, the parent
  RegularPointBlowupFunctions module, LocalSurfaceMaximalBlowupGeometry,
  RegularPointBlowupGeometry and SurfacePointBlowupData. Those modules state
  different conclusions (functions, regularity/exceptional geometry or tower data),
  not this combined package. Their existing constructions are reused as appropriate.
- Exact blueprint-ID grep in lean/WeilConjectures: no declaration for this item.
  Exact searches for pointBlowupLocal, pointBlowupRatio and
  point_blowup_local_chart_package in both source roots and
  dag/lean_names_upstream.json: no preexisting names.
- Read AffineBlowup.chartFrac and IdealSheafData.blowupChart when checking for a
  preexisting ratio-ring chart map. They use homogeneous-localization chart rings;
  ratioChart only composes the existing chart with the existing coefficient
  equivalence, as required for the ratio subalgebras in this item.

No STATEMENT-DISPUTED finding and no statement correction. The example
CompactObject.lean is now withdrawn and contains no declarations; this delivery
uses the live module/public-import/expose conventions from brief-stage2 §3–4.

Validation: scompile.py compiled this file both as a sandbox module and under its
actual library module name with no errors and no warnings. All variables and
universes are bound explicitly. Dry-run and delivery results follow below.

## Second reading by Q127

The delivered section under this heading was a self-review by the worker who wrote the
statement (H11). The maintainer's second reader (cc review service, 2026-10-24) replaced it
with the reading below.

Node clauses and their Lean renderings:

1. T regular, dim T ≤ 2, x a closed point: `(T : Scheme.{u}) (hregular : IsRegularScheme T)
   (hdim : topologicalKrullDim T ≤ 2) (x : T) (hx : IsClosed {x})`. Exact. There is no global
   Noetherian or quasi-compact hypothesis.
2. The reduced centre and W = Bl_x T: `vanishingIdeal ⟨{x}, hx⟩`, with `.blowup` and
   `.blowupMap` from def-nagata-global-blowup. Exact.
3. The affine neighbourhood V = Spec R with R Noetherian and regular: `∃ V : T.affineOpens,
   x ∈ V`, `IsNoetherianRing Γ(T,V)`, `IsRegularRing Γ(T,V)`. Exact.
4. 𝔭 maximal; A = O_{T,x} ≅ R_𝔭; 𝔪 = 𝔭A: `primeIdealOf.IsMaximal`, `∃ e` with
   `e ∘ algebraMap = germ` (this pins e), and `Ideal.map germ 𝔭 = maximalIdeal`. Exact.
5. f : b⁻¹V → V is proper: `IsProper (blowupMap ∣_ V)`. Exact.
6. A is a regular local domain and d ∈ {0,1,2}: `IsRegularLocalRing`, `IsDomain`, and a
   three-way `ringKrullDim` disjunction. Exact.
7. Z ≅ Bl_𝔪(Spec A) = Proj R_A(𝔪) over Spec A, through the canonical flat comparison with
   the factors exchanged:
   - `e` is pinned by both projections, so it is the canonical exchange/associativity map.
   - The middle map is the published `blowupFlatBaseChangeIso` (= `asIso blowupFlatBaseChange`,
     the recorded declaration of def-nagata-blowup-flat-base-change-map, read in the live source).
   - `ea` is pinned by its inverse, `AffineBlowup.hom (ΓSpecIso) hm ≫ J.blowupι ⊤`, which is
     the singleton-cover comparison.
   - The over-base equations state the agreement of the coefficient maps.
   - `AffineBlowup m` is by definition `Proj (reesGrading m)`.
   Exact.
8. The closed fibre: `ef`, pinned by `fiberι` and `fiberToSpecResidueField`. Exact,
   including the empty case.
9. d = 0 gives `m = ⊥ ∧ IsEmpty model`; d = 1 gives `IsIso projection`. Exact.
10. d = 2, "choose s,t generating 𝔪; they are nonzero, form a regular sequence, and the charts
   … hold". The delivered `TwoCharts` was `∃ s t, …`. That is weaker than the node, which
   asserts these properties for whatever generators are chosen. **Changed**: `TwoCharts` is
   now (∃ generators s,t) ∧ ∀ s t ∈ 𝔪 with 𝔪 = (s,t), the nonzero, regular-sequence, chart,
   overlap and A_st clauses. The existence conjunct keeps "choose", which presupposes that
   generators exist, so citers that only need some pair of parameters keep a direct
   interface. The fix is true: in a 2-dimensional regular local ring every generating pair
   is a regular system of parameters (00NQ), and step 7 of the proof uses only this.
11. The chart clauses: `es/et` are pinned by `ratioChart` (Spec of θ_s, then the Proj chart).
   The structure equations hold over Spec A, and the cover is `Us ⊔ Ut = ⊤`. `rs/rt` are
   pinned to t/s and s/t. The intersection is equal to both basic opens. ψ is pinned on A,
   and on the restrictions from Us and Ut, against the natural maps C_s ⊆ A_s → A_st and
   C_t ⊆ A_t → A_st. The A_st equality holds for every section. Exact. ψ is not an
   arbitrary choice, because Γ(Us⊓Ut) is a localization of C_s.

Edge cases: empty T (the statement is vacuous). Spec k (d = 0, empty Z). A DVR (d = 1).
k[s,t]_(s,t) (d = 2). Disconnected or non-quasi-compact T. A universe u is arbitrary.

Searches: the worker's recorded searches, together with a reading of
WeilConjectures/Blowup/{FlatBaseChange,Gluing,Affine/Defs,Affine/ChartAlgebra}.lean in
side-live. No existing package statement was found.

Compile: the fixed module compiled through `nt_compile.py --json` with no errors or warnings
(3.5 s). The theorem signature and `lean.statement` are unchanged.
