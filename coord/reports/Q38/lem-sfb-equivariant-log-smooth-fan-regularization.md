## Worker report

The new module `Sheaf.AlgebraicGeometry.EquivariantLogSmoothFanRegularization` states
`AlgebraicGeometry.exists_equivariant_log_smooth_fan_regularization`, with `sorry`
as its only postponed proof. Its helper structure
`AlgebraicGeometry.EquivariantLogSmoothFanRegularization` packages exactly the
geometric and equivariant conclusions for a specified existing log blowup tower.
It constructs no object by choice and contains no postponed data.

The item's natural-language statement, source and proof are unchanged. The statement dependencies cite the already recorded procedure, composite, action,
and fan-chart definition nodes. The new definition ownership node
`def-sfb-relative-normal-crossings-chart` records the existing chart and intersection
ideal declarations. The criterion theorem is retained in `proof_deps` only.
There are no new Lean declarations beyond the original delivered module and no
dependency modules.

I read the item, every statement dependency and its Lean record or Mathlib match,
the declarations used below with their docstrings, and the relevant existing
regularization statements. The example CompactObject file is now a withdrawn
module; its node records the upstream compact-object notion. I followed the current
module-mode convention from the stage brief and the live log-geometry modules.

Source checked directly in the local ILO PDF: VIII Remark 3.3.13, Theorem 3.3.15
and its descent proof (printed pp.108--110); VIII 3.4.4--3.4.9 (pp.110--112);
and X Lemma 2.2 and its smooth-pair-over-a-field refinement (pp.149--150).
The module's ten-step proof docstring follows the node's ten steps, including the
finite open-subfan reduction, strict chart comparison, center descent, group laws,
ordinary blowup/normalization identification, bundle-projectivity, unchanged open,
log smooth composition, and relative smooth coordinate charts.

### Hypotheses, one by one

| Node hypothesis | Lean rendering |
| --- | --- |
| Arbitrary field F | `(F : Type u) [Field F]`; no perfectness or characteristic condition |
| Integral scheme X | `(X : FineSaturatedLogScheme.{u}) [IsIntegral X.scheme]` |
| Finite type over F | `[LocallyOfFiniteType s.base] [QuasiCompact s.base]` |
| Closed B and dense complement U | `B : Closeds X.scheme`, `U : X.scheme.Opens`, `hUB`, and `hU : DenseRange U.ι` |
| Divisorial log structure | `hdiv` is an isomorphism to the existing `divisorialLogPresheaf U.ι`, commuting with its actual inclusion into regular functions |
| Fine saturated | Fields `X.logStructure` and `X.fineSaturated` of the existing bundled log scheme; no copy of the log definitions |
| Log regular pair | `hpair : IsDivisorialFineSaturatedLogRegularPair ... hU`, with the existing local-Noetherian certificate `X.locallyNoetherian` |
| Triviality locus exactly U | `htriv : X.logStructure.trivialityLocus = (U : Set X.scheme)` |
| Trivial logarithmic base field | `N`, its fs certificate `hN`, and `hNtriv : N.trivialityLocus = Set.univ`; the scheme is exactly `Spec (.of F)` |
| Log smooth over that base | The actual log structure map `s` and `hs : s.IsLogSmooth` |
| Finite group J | `(J : Type v) [Group J] [Finite J]`, independent of the scheme universe |
| Compatible action on X and F | `a : J →* Aut X.scheme`, `ρ : J →* (F ≃+* F)`, and `hscalar` |
| Semilinear rather than necessarily F-linear | The scalar arrow is `Spec.map (CommRingCat.ofHom (ρ g⁻¹).toRingHom)`; inverse is required by contravariance and the `Aut` multiplication convention |
| Boundary preserved | `hB : ∀ g, (a g).hom '' (B : Set X.scheme) = B` |

Local Noetherianity and fs are certificates in the existing bundled log-scheme
interface. The former follows mathematically from the finite-type-over-a-field
hypothesis; it introduces no geometric restriction. The model `N` is identified
as the trivial structure, rather than allowing an unspecified logarithmic base.
The sheaf isomorphism `hdiv` commutes with structural maps, so no arbitrary log
structure is substituted for the divisorial one.

### Conclusions, clause by clause

| Node conclusion | Lean rendering |
| --- | --- |
| Finite tower of saturated log blowups starting at X | `(P.tower X hX).tower : SaturatedLogBlowupTower` and its `initial` equality, through `LogBlowupTowerOver` |
| Nonempty coherent ordered log centers | Existing `tower.center` and `tower.isBlowup`; `IsSaturatedLogBlowup` includes `IsNonemptyCoherentIdeal` |
| A saturated smooth-functorial fan desingularization | Existential `R : FineFan.SmoothFunctorialDesingularization` |
| Agreement on every strict etale fan-chart neighborhood | For every Y admitting a strict etale map to X and every finite admissible chart fan H, the theorem lifts `R.resolution H` to `LogFanTower`, fixes its initial chart by `HEq`, and gives `LogBlowupComparison` over the log identity with `P.tower Y hY` |
| Contracted pullback and ordered-center preservation | `LogBlowupComparison.count`, `retained`, `cartesian`, `centers`, and `whole`; exactly whole-monoid centers are deleted, including consecutive ones |
| Composition and finite disjoint unions | `P : StrictEtaleLogBlowupProcedure` includes identity/composition equations on actual maps and indices. Its domain is all strict etale neighborhoods of X, without requiring them quasi-compact. It contains finite disjoint unions of such neighborhoods, and its comparison covers every component inclusion |
| J-action on all stages respecting group law | Helper `originalAction`, `originalBase`, and `action`; the existing `FSLogGroupAction` supplies identity and multiplication laws on actual log section maps |
| Equivariant tower and invariant centers | Helper `equivariant`, `stepEquivariant`, `centersInvariant`; these use the actual stage composites and arrows |
| Compatibility with the given scalar action at each stage | Helper `semilinear`, with the same `ρ` as in the hypothesis |
| Generated nonzero finite-type ring ideal at each stage | `normalized` supplies `I`, `I ≠ ⊥`, `I.ofFiniteType`, and the equality of its geometric stalk ideal with the span of the structural images of the actual log center |
| Normalization of the ordinary blowup | `normalized` supplies `hI : IsIntegral I.blowup` and an isomorphism of the next scheme with `@Scheme.normalization I.blowup hI`; its composite with `fromNormalization` and `I.blowupMap` is the actual stage arrow |
| Every normalization map finite | `IsFinite (@Scheme.fromNormalization I.blowup hI)` in `normalized` |
| Common function field | Normalization is the recorded function-field normalization of the integral blowup. Every stage is integral and the actual composites restrict to isomorphisms on the same dense open, so their induced function fields are canonically the original one; no unrelated field is supplied |
| Integral Noetherian finite-type stages | Helper `integral`, `noetherian`, `finiteType`; `IsNoetherian` is Mathlib's local-Noetherian-plus-compact class |
| Projectivity in the bundle sense | Helper `projective : IsProjectiveBundle ...`; this is the recorded relative Proj of the symmetric algebra of a finite-type quasi-coherent module, not finite projective space |
| Birationality and isomorphism over U | `unchangedOpen` gives `IsIso (a_i ∣_ U)` for every actual stage composite; `denseOpen` makes the terminal preimage dense, while `hU` makes U dense. Thus these are the same dense opens and the usual birationality statement |
| Log regularity at every stage | Helper `logRegular` |
| Log smoothness over F at every stage | Helper `logSmooth`, applied to the actual composite `(A.toBase i).comp s` |
| Exact pulled-back triviality loci | Helper `triviality` is equality with the full inverse image of U |
| Free final characteristic monoids | Helper `freeCharacteristic`: every geometric characteristic is multiplicatively equivalent to `Multiplicative (Fin r → ℕ)` for some `r : ℕ` |
| Regular final scheme | Helper `regular : IsRegularScheme ...` |
| Smooth final F-scheme | Helper `smooth : Smooth ...` for the actual structural composite |
| B_n is the reduced inverse image of B | Helper `boundary` identifies the radical of the pulled-back reduced boundary ideal with the reduced induced ideal of the complement of the pulled-back U |
| Smooth maps to affine r-space and divisorial N^r chart | Helper `charts` uses the already existing `RelativeNormalCrossingsChart` for the actual final F-map and pulled-back U. Its fields give an etale neighborhood with a geometric lift, a smooth comparison to `AffineSpace (ULift (Fin r)) (Spec F)`, the actual coordinate log chart, and the product equation as equality of ideal sheaves |
| All r local branches through the chosen point | First conjunct inside `charts` puts the lifted point in every coordinate zero locus |
| Smooth intersections, expected codimension | The final conjunct of `charts` quantifies every coordinate subset `z`, makes its actual scheme-theoretic intersection smooth over F, and says every minimal prime over its ideal has height `z.card` in each ambient affine chart |
| No separatedness or perfection; self-intersections allowed | Neither is a hypothesis. Coordinates are chosen only on etale neighborhoods, and no global branch labels or irreducible global components occur |
| Length zero and empty boundary allowed | Existing tower length is any natural number; free rank is any natural number; empty coordinate products and subsets are allowed |

The theorem's neighborhood domain is written as the explicit property
`∃ q : EtaleLogHom Y X, q.IsStrict ∧ Etale q.base`. In particular, it does not
silently restrict all strict etale tests to quasi-compact schemes. The fan argument
uses `FineFan.ResolutionInput`, the existing finite-affine-cover admissibility
convention of the node's fan-resolution dependency. Affine fan-chart neighborhoods
are included, and the finite open-subfan reduction in the node's proof makes the
choice of an admissible fan target immaterial.

### Recorded dependency declarations used

All names in the following table are in `AlgebraicGeometry` unless explicitly
prefixed otherwise; the listed module is imported publicly when used in the type.

| Node | Module and declaration |
| --- | --- |
| def-weil-field | Lean/Mathlib `Field` |
| def-pc-integral-scheme | `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral` |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact` |
| def-trf-log-regular-pair | `Sheaf.AlgebraicGeometry.LogRegularPair`: `IsDivisorialFineSaturatedLogRegularPair`, `divisorialLogPresheaf`, `divisorialStructuralMap`, `strictLocalGerm` |
| def-trf-fs-log-blowup | `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`, `EtaleLogHom`, `IsSaturatedLogBlowup`, `SaturatedLogBlowupTower`, `characteristic`, `trivialityLocus`, `idealStalk` |
| def-per-fs-log-smooth-etale | `Sheaf.AlgebraicGeometry.FSLogSmoothEtale`: `EtaleLogHom.IsLogSmooth` |
| def-per-log-fan-chart-tower | `Sheaf.AlgebraicGeometry.LogFanChartBlowup`: `LogFanChart`, `LogFanTower`, `LogFanChart.pullbackIdeal` (the existence theorem remains cited by the original source statement and proof) |
| def-trf-fine-fan-blowup | `Sheaf.AlgebraicGeometry.FineFanBlowup`: `FineFan.ResolutionInput`, `FineFan.SmoothFunctorialDesingularization` |
| def-sc-normalization | `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `Scheme.normalization`, `Scheme.fromNormalization` |
| def-nagata-global-blowup | `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap` |
| def-trf-projective-bundle-morphism | `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `IsProjectiveBundle` |
| def-weil-regular-scheme | `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` |
| def-weil-etale-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` |
| def-sbc-affine-space | `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, `AffineSpace.coord` |
| def-weil-pbc-scheme-reduction | `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.IdealSheafData.subschemeι`, together with the existing radical-ideal construction |
| pqf-def-locnoeth | `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian` |
| def-trf-strict-etale-log-blowup-procedure | `Sheaf.AlgebraicGeometry.StrictEtaleLogBlowupProcedure`: `StrictEtaleLogBlowupProcedure`, `LogBlowupTowerOver`, `LogBlowupComparison` |
| def-per-strict-log-blowup-procedure | `Sheaf.AlgebraicGeometry.StrictLogBlowupProcedure`: `LogBlowupTowerOver.toBase` |
| def-per-fs-log-group-action | `Sheaf.AlgebraicGeometry.FSLogGroupAction`: `FSLogGroupAction`, `FSLogGroupAction.IsEquivariant` |
| def-sfb-relative-normal-crossings-chart | `Sheaf.AlgebraicGeometry.FreeCharacteristicRelativeNCCriterion`: `RelativeNormalCrossingsChart`, `RelativeNormalCrossingsChart.intersectionIdeal` |

The finite-type ideal predicate is the existing `Scheme.IdealSheafData.ofFiniteType`
from `WeilConjectures.Compactification.FiniteTypeExtension`, not a copy. All stated
proof-dependency modules are also imported, with plain imports for proof-only
material. The node's Mathlib-leaf proof dependencies use the existing composition,
base-change, Noetherianity, etale precoverage and quasi-separatedness APIs.

### Searches and duplicate check

The prescribed `msearch.py` searches are recorded in the sandbox `searches.jsonl`.

- LeanFinder query: `equivariant saturated log blowup resolution log regular log smooth scheme free characteristic monoids`. Eight hits, all ordinary smoothness APIs; no logarithmic equivariant regularization theorem.
- Loogle query: `FineSaturatedLogScheme, SaturatedLogBlowupTower, SmoothFunctorialDesingularization`. Zero hits; the index does not know the project-specific identifier `FineSaturatedLogScheme`.
- Mathlib grep query: `LogBlowup|LogRegular|Fan.*[Rr]esol`, under `AlgebraicGeometry`. Zero hits.
- LeanSearch query: `A log regular log smooth scheme over a field admits an equivariant saturated log blowup tower with free characteristic monoids`. Eight hits concerning schemes and ordinary smoothness/formal etaleness, none this statement.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf`, and of `dag/lean_names_upstream.json`, for the item id and proposed declaration names found no existing declaration. Broader `LogBlowupTower`, log-regular and fan-resolution searches located the reused interfaces listed above.
- `tools/blueprint_refs.py search 'log smooth fan regularization'` returned zero blueprint matches.

I also read `GabberLogBlowupRegularization`, `MonoidalResolutionTower`,
`InducedNormalizedLogResolution`, and `RigidifiedQuotientTowerComparison` for overlap.
The first imposes separatedness and does not give this relative-field statement;
the second lacks the full equivariance, chart comparisons and scheme geometry;
the rational induced-rule interface has a different input resolution algorithm;
the last concerns quotient-tower comparison. None is an exact existing match.
Their existing underlying notions are reused rather than redefined. The new helper
structure is the package of this node's conclusion, not another definition of log
regularity, blowups, actions, normalization, projectivity or normal crossings.

### Edge cases and validation

- `length = 0`: `Fin length` has no arrows or centers; the single stage and its
  actual base composite remain valid. There is no positive-length condition.
- `B = ∅`, points off B and `r = 0`: the coordinate product is 1, the boundary
  ideal is the unit ideal, the characteristic is the zero additive monoid, and
  the comparison is to affine zero-space. Empty coordinate subsets give the whole
  neighborhood, expected codimension zero, and its ordinary smooth F-map.
- The empty input scheme is already excluded by the node's integrality hypothesis;
  no additional nonemptiness assumption is introduced.
- The trivial finite group, positive characteristic, imperfect fields and nontrivial
  scalar actions all remain within the binders. No group-order invertibility or
  tameness is assumed.
- No separation hypothesis appears on X or its structure map. Global boundary
  self-intersections are not excluded by a global SNC-component decomposition.
- The quasi-coherent center is fixed on every pointed etale stalk, not just by its
  radical or support. This prevents a different ordinary blowup center from being
  substituted. Normalization finiteness is an output, not built into normalization.
- Universes `u v` and all variables are bound; `autoImplicit` and
  `relaxedAutoImplicit` are both disabled. The first command is `module`.

The initial compile exposed a missing public import for the existing finite-type
ideal predicate. Adding its owning upstream module resolved it. The final delivered
file compiled in both sandbox and actual module-name modes through `scompile.py`,
within the unmodified 60-second limit, with no errors or warnings. Only the main
theorem has `sorry`. No theorem was proved, and no live source or build was modified.
No statement correction or STATEMENT-DISPUTED issue was needed.


## Returned delivery repair

The immutable returned head was `c3703b131edc`. The maintainer found one H2 record
fault and explicitly judged the mathematical statement and its edge cases sound.
The sandbox module remains byte-for-byte unchanged, SHA256
`8f920fa3d8114a7c732c91760e5be39202554abc336866d7f6fa2b7e21b5b629`.
The current main item has its original statement/dependencies and no Lean record;
this repair rebases the authorized Lean record and statement-dependency additions
onto that current node, preserving all other main fields. The delivery wrapper
bases its commit on current main.

1. H2: replace `lem-sfb-free-characteristic-relative-nc-criterion` in `stmt_deps`
   by `def-sfb-relative-normal-crossings-chart`. The new definition node has an
   `existing:true` record naming the exact existing plain declarations
   `AlgebraicGeometry.RelativeNormalCrossingsChart` (line 84) and
   `AlgebraicGeometry.RelativeNormalCrossingsChart.intersectionIdeal` (line 116)
   in `Sheaf.AlgebraicGeometry.FreeCharacteristicRelativeNCCriterion`. I reread
   both full definitions: neither uses or chooses data from the theorem at
   line 291. The theorem remains in `proof_deps`. No Lean declaration was copied,
   moved, or modified.
2. Advisory: add landed `def-per-log-fan-chart-tower` to `stmt_deps`. Its
   `existing:true` record owns the existing `LogFanChart`, `LogFanTower` and
   `LogFanChart.pullbackIdeal` declarations. The original
   `lem-trf-log-fan-chart-blowup` citation is retained because the original source
   statement names its fan-chart/pullback existence theorem and the proof needs
   that theorem; ownership of the plain structures now cites their definition
   node explicitly. No original source statement or proof citation is removed.

## New nodes

`def-sfb-relative-normal-crossings-chart` is an ownership record, with
`existing:true`, for the pointed chart and its coordinate-intersection ideal in
`Sheaf.AlgebraicGeometry.FreeCharacteristicRelativeNCCriterion`. Source: ILO VI
1.1/1.4/1.6; X 1.2, printed pp.136--138; VIII 4.2.2(i) and X 2.2 for intersections.
The node defines the data of a chart, not existence, freeness, smoothness of all
intersections, or the requirement that every branch pass through the chosen point.
Those extra properties remain in the fan-regularization conclusion. The node's
Lean signature is copied verbatim through the `where` boundary; its second
recorded declaration is the actual `ofIdealTop (Ideal.span ...)` construction.

Clause audit of the new node against the existing declarations:

- Field F, scheme X over F, open U, geometric point: the binders
  `{F} [Field F] {X} (f) (U) {Ω} [Field Ω] [IsAlgClosed Ω] (t)`.
- Etale neighborhood and chosen lift: fields `W : X.Etale` and `point`.
- Nonnegative rank and smooth F-coordinate map: `r : ℕ`, `comparison`, `over`,
  and `smooth`. Coordinates have index `ULift (Fin r)`.
- Divisorial monoid chart: `chart` maps to the already constructed
  `divisorialSections U.ι W`; `coordinates` fixes each generator as the actual
  pulled-back affine coordinate, and `isChart` checks the actual divisorial stalk
  pushout condition at every pointed geometric stalk.
- Reduced boundary product equation: `boundary` is equality of the reduced
  induced `vanishingIdeal` with the principal product-coordinate ideal, not only
  equality of supports.
- Intersection ideal: `intersectionIdeal C s` is `ofIdealTop` of the ideal span
  of precisely the pulled coordinates indexed by `s`. It contains no theorem
  choice or postponed data. Empty `s` spans the zero ideal and gives the entire W.
- Rank zero and an empty boundary are allowed; the empty coordinate product is 1.
  A general chart need not have every coordinate vanish at its pointed lift.
  The item's `charts` conclusion still imposes that property explicitly.

Searches, repeated for this missing definition owner and recorded verbatim in its
`mathlib_searches`: LeanSearch `relative normal crossings chart smooth map affine
space divisorial log chart` returned eight ordinary smoothness results;
LeanFinder `RelativeNormalCrossingsChart intersectionIdeal coordinate branch
intersections` returned eight unrelated chart/zero-locus results; Mathlib grep
`RelativeNormalCrossingsChart|intersectionIdeal|NormalCrossings` under
`AlgebraicGeometry` returned zero hits. `rg` in both project source trees and the
upstream-name index found only the exact plain declarations in the cited module.
Searching the DAG for their declaration names and the proposed id found only the
criterion theorem node; there was no definition owner. The blueprint search
`relative normal crossings chart` returned zero matches. Consequently the repair
adds only a DAG definition record reusing those declarations, with no module.
The ancestor tool still reports `blueprint.from.node = None`, inherited exactly
from the item's accepted ancestry, and the item's id is prepended to `via`.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
