## Worker report

The delivery states `WeilConjectures.GlobalVerdierDuality.global_verdier_duality` in
`Sheaf.Paper.GlobalVerdierDuality`. Its single postponed proof is `sorry`; every helper has
real data. The statement and proof plan of the item are unchanged.

Hypotheses, clause by clause:

- The fixed finite-field datum is `D : FiniteFieldDatum.{u}`. Its fields give the specified
  finite field and its algebraic closure. `l`, `[Fact l.Prime]`, `hl : l ≠ D.p`, and the field
  `Ω` with its `Padic l` algebra and `IsAlgClosure` give the coefficient convention. The
  existing `Stage.{u} l` indexes positive finite quotients, integral coefficients, finite
  coefficient fields and the algebraic closure; `FieldStage` includes finite dimensionality.
- `X : Scheme.{u}` and `[X.Over (Spec (.of D.k))]` give the structure morphism.
  The `Smooth`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` and
  `GeometricallyConnected` instances render precisely smooth, separated, finite type,
  geometrically connected. Finite type is locally finite type plus quasi-compact.
  `d : ℕ` and `_hd : X.IsPureDimension d` render pure dimension d.
- `_hX : GeometricAlternative ...` is the actual disjunction. Its first branch is
  `IsProper` of the structure morphism. Its second branch existentially gives an object
  `X₀` over `Spec k₀`, smooth, separated, locally finite type, quasi-compact and
  geometrically connected, and an isomorphism over `Spec k` to `D.geometricFiber X₀`.
  That branch has no properness condition. The isomorphism is over the base, not just an
  isomorphism of the underlying topological spaces or schemes.
- There is no admissibility, ambient exceptional-adjoint, projection-formula or duality
  hypothesis. `Assertion` universally quantifies over the already constructed normalized
  `ConstructibleExceptionalCoefficients.System` and a compactification. The independent
  `exists_system` theorem supplies these systems; the quantifiers express independence
  of those choices. All closed structures, comparisons and isomorphisms are OUTPUT.

Conclusions, clause by clause:

- At each `s : Stage l`, `C l Ω X s` is exactly the dependency's full constructible finite-Tor
  category; at rational/common stages it is the constructible category. Thus every K in
  the node's domain is covered. `A.ring.operation c s` is the actual compact-support
  adjunction. Its `F` is Ra_! and its `G` is the unconditional constructible Ra^!.
- `Data` is an abbreviation for the EXISTING `VerdierExchange.StageData`, with F on both
  occurrences of the structure map, and the literal `identityOperation` at the point.
  Therefore `d.dualY` is internal Hom into the coefficient unit, exactly coefficient dual;
  `d.dualX` is internal Hom into `F.G.obj unit`, exactly Verdier dual, with
  omega_X = Ra^! Lambda_s. No second internal-Hom or Verdier-dual construction is made.
- `Conclusion.exchange.epsilon` is a NATURAL isomorphism
  `F.F.op ⋙ d.dualY ≅ d.dualX ⋙ d.star`. `StageConclusion.components` says its components
  are `d.epsilon`, the already defined projection/evaluation/adjunction transpose.
  `Conclusion.dualizing` fixes its dualizing comparison to the identity, excluding an
  arbitrary automorphism of omega_X. `RingProjection` fixes projection to the canonical
  proper-counit/open-projection map and `RingRealization` fixes Hom and evaluation to the
  actual original small pro-etale site, with site object/morphism sizes u+1 and u.
- `RingRealization.star` identifies `d.star` with the ordinary derived direct image.
  Thus the displayed isomorphism is `(Ra_! K)^vee ≅ Ra_* D_X K` in the constructible
  POINT category. This is the node's expressly permitted point-category formulation of
  RΓ_c and RΓ. Under its recorded `pointFiniteFibre`, `pointIntegralFibre`,
  `pointRationalFibre`, `pointQbarFibre` and the ordinary/compact section definitions,
  it reads exactly `RΓ_c(X,K)^vee ≅ RΓ(X,D_X K)`. It is an isomorphism of objects, not
  merely an equality of dimensions or a cohomological pairing. The finite-Tor point
  category is a FULL subcategory of the bounded constructible point category; an
  isomorphism between these objects is the same there.
- Naturality on all K and all morphisms is part of the functor isomorphism, contravariant
  in K because its source is the opposite category.
- Shift compatibility is `StageConclusion.shift`, with its two dual shift structures,
  ordinary-image shift structure and the normalized `RingShiftRealization`. The latter
  fixes the actual signed Hom-complex comparisons; shifts of K give opposite shifts.
- `Package.ringScalar` uses the system's actual scalar functors. Its equation identifies
  q with the actual `A.ring.comparison` q; that comparison already has the canonical
  proper/open normalization. The unit equation fixes the actual derived scalar unit.
  `ScalarConclusion.exchange` is the commuting square for epsilon, with the evaluation-
  transposed Hom map and the ordinary direct-image mate. `ScalarShifts` includes its
  compatibility with shifts. `Allowed` covers nonflat finite reduction (including equal
  exponents), integral reduction and integral finite-field scalar extensions.
- `Package.rationalization`, `.rationalScalar`, `.common` give the corresponding squares
  for the actual rationalization, field extension, and common-stage inclusion. Each
  exceptional comparison is identified with the corresponding system comparison.
  Thus all four coefficient stages are included, not only a finite-ring specialization.
- For K = Lambda_X, `Conclusion.unitIso` has the explicit evaluation and coevaluation
  maps `unitEvaluation` and `unitCoevaluation`, defined by the right unitor and the
  closed adjunction. `Conclusion.constant_hom` fixes the constant-coefficient iso to
  the SAME epsilon component followed by `d.star.map unitIso.hom`. Its target is
  exactly Ra_* omega_X. `Package.unitX`, `.unitY` identify these tensor units with the
  coefficient objects; the two normalization equations fix their right-unit constraints
  against the ordinary ringed-site tensor unit, rather than arbitrary unit isomorphisms.

Dependency declarations read and used:

- `sk-def-sf-setting`: `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`,
  `AlgebraicGeometry.Etale.constantComplex`, `DerivedCategoryModule`,
  `DerivedCategory.boundedConstructibleFiniteTor`, `hasTorAmplitudeIn`; the pro-etale
  all-stage specialization uses the existing `ConstructibleExceptionalCoefficients.C`.
- `sk-def-sf-operations`: its closed slopmaster2 audit supplies the recorded upstream
  `Etale.upperStar`, `rightDerivedLowerShriek`, `rightDerivedUpperShriek`, `derivedTensor`,
  `derivedHom`, `openImmersionLowerShriek`. The actual concrete pro-etale constructible
  interface here is `ConstructibleExceptionalCoefficients.System`, `Operation` and
  `exists_system` in `ConstructibleExceptionalAdjunctionCoefficients{Data,}`. It is
  publicly imported by the existing exchange interface; no operations dependency is
  restated and no optional ambient adjoint is used.
- `def-sf-pf`: see the existing-declaration interface repair below. The actual dual
  notation used is `VerdierExchange.StageData.dualX`, `.dualY`; the projection is the
  existing `PurCompactSupport.projectionMap` and `RingProjection`.
- `def-weil-finite-coefficient-point`: `Sheaf.Paper.FiniteCoefficientPoint`,
  `pointFiniteFibre`, `pointIntegralFibre`, `pointRationalFibre`, `pointQbarFibre`.
- `def-weil-ordinary-compact-cohomology`:
  `Sheaf.Paper.CommonStageCompactWeilCohomology`, its public ordinary/compact interface,
  in particular `finiteOrdinarySections`, `finiteCompactSections`,
  `integralOrdinarySections`, `integralCompactSections`, the rational and common-stage
  counterparts. Their source definitions are point fibre after the corresponding
  actual structure-morphism direct image. The primary `commonStageCompactWeilCohomology`
  also retains the Weil structure for its additional specialization; it is not confused
  with the general complex-valued statement used here.
- Smooth: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
  Geometric connectedness: `Mathlib.AlgebraicGeometry.Geometrically.Connected`,
  `AlgebraicGeometry.GeometricallyConnected`, as explicitly allowed by the dependency
  record `def-pc-geometrically-irreducible`.
- Pure dimension: `Sheaf.AlgebraicGeometry.PureDimension`, `Scheme.IsPureDimension`.
- Morphism conventions: `Smooth`, `IsProper`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`. The convention-only node has no separate definition.
- Base change: `FiniteFieldDatum.geometricFiber`, the existing `Over.pullback`
  specialization of `def-pc-base-change`. No alternative base-change construction.
- Proof-only imports: `VerdierExchange`, `FiniteTorStability`, `PointFibreDerivedTensor`,
  `PointFibreEquivalence`, `PointSectionsDerivedReduction`, and the recorded upstream
  `PoincareDuality.Degreewise` point lemma. Point scalar extension and the fibre definitions
  are already public dependencies of `FiniteCoefficientPoint`.

Edge cases checked before and after writing: X=Spec k with d=0 reduces to the tensor/Hom
unit identification. K=0 is included as an object of every finite-Tor domain, with no
nonzero or dualizability assumption. The empty scheme is correctly excluded by geometric
connectedness (and pure dimension alone does not exclude it). Nonproper A¹ and G_m over
k₀ satisfy the second branch, with no imposed properness. Every positive exponent occurs
via `ℕ+`, including exponent one and the identity reduction; exponent zero was never in
the source. Torsion integral objects and nonflat quotient maps are included. Negative
shifts are included by the ℤ shift law. Schemes and all original site universes retain
the common larger-universe convention; no site object/morphism universe equality is added.

Searches (2026-10-19 UTC):

- `msearch.py ... leanfinder`: “Global Verdier duality identifies coefficient dual of
  compactly supported cohomology with cohomology of Verdier dual naturally in complexes”.
  Eight unrelated results on derived cohomological bounds, group cohomology/Ext and
  Hom-complex cohomology; no match.
- `msearch.py ... loogle`: `coefficientDual, verdierDual, rightDerivedLowerShriek`.
  Zero hits; unknown identifier coefficientDual.
- `msearch.py ... grep`: `Verdier|coefficientDual|compactlySupportedGlobalSections`,
  subdirectory `AlgebraicGeometry`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `globalDual|global_dual|` plus the
  blueprint id and `coefficientDual_rightDerivedLowerShriek`: upstream GlobalDuality
  found and read in full. It covers only finite coefficients in the ambient etale category;
  its own docstring explicitly says its shift construction is only the object-level form,
  not the compatibility equation. It omits higher coefficients and their comparison
  squares. Thus its Nonempty theorem is not an exact existing match. The existing
  `coefficientDualRightDerivedLowerShriekIso` and unit specialization were also read.
- `rg` found the existing concrete `VerdierExchange` stage, realization and comparison
  records, which are reused. The DAG was searched/read for the item's dependencies and
  their current records. No independent missing notion or new DAG node is introduced.

No STATEMENT-DISPUTED flag or item statement correction is needed.

## Dependency modules

No dependency module is included in this repaired packet. The retained item module uses the
concrete existing `VerdierExchange.StageData` interface directly: `dualX` is the Verdier
dual, `dualY` is the coefficient dual for the literal `identityOperation`, and the existing
projection interfaces supply the compactification map. The separate `def-sf-pf` packet was
dropped per H13 because its duplicate abstract notation would replace the landed NA record.
The item node's `lean.note` records the concrete reuse (`ω_X = F.G.obj unit`,
`StageData.dualX`, and `StageData.dualY` with `identityOperation`). No new dependency node
or duplicate construction is written.

## Second reading by O4

I reread the node and final module clause by clause as a separate worker check. The
geometry uses the actual structure map; the descended alternative retains all five X₀
properties and its isomorphism over k. The canonical arrow is the published epsilon,
with the literal identity adjunction at the point and identity dualizing comparison.
The coefficient square is an equation for that arrow; the shift clause is an equation,
not just existence of shifted object isomorphisms. The unit specialization uses its same
component. The four stages use the original finite-Tor categories and normalized actual
operations, without an ambient admissibility condition. During this pass I added the
right-unitor normalization equations for the coefficient units; these exclude free
choices of unit identifications in the realization. I also replaced the unusably
specialized abstract dual-notation record by the existing concrete interface, rather
than adding a SixFunctorDatum assumption. The single sorry is the item's named theorem.
The independent maintainer review is the review of this delivery.

Validation: prescribed scompile.py checked the final module both as a sandbox file
(22.1 seconds) and under its actual library name (14.1 seconds), cleanly. No non-sorry
warnings. An earlier elaboration timeout was repaired by retaining the source interface's
`backward.isDefEq.respectTransparency.types false` option; the final check uses the
unchanged 60-second limit. The repaired packet changes the item node's `lean.note`; the duplicate `def-sf-pf` node file is removed, while the item Lean module is retained unchanged.
