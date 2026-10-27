# AlgebraicGeometry.AlgebraicSpace.representableWith_baseChange

## Reason

The returned delivery duplicated this private theorem in
`AlgebraicSpaceFlatLfpUniversallyOpen`. Expose the existing proved theorem in its
unclaimed `ChartwiseEtalePermanence` module so the assigned module can import
and use it. This follows the return request to reuse the existing theorem.
The helper has the identical statement and proof; no mathematical statement or
definition changes. No source-library module is modified.

## Old

```lean
private theorem representableWith_baseChange {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) {A B C D : (Over S)ᵒᵖ ⥤ Type u}
    {q : D ⟶ A} {p : D ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (sq : IsPullback q p f g) (hf : IsRepresentableWith P f) :
    IsRepresentableWith P p
```

## New

```lean
theorem representableWith_baseChange {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) {A B C D : (Over S)ᵒᵖ ⥤ Type u}
    {q : D ⟶ A} {p : D ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (sq : IsPullback q p f g) (hf : IsRepresentableWith P f) :
    IsRepresentableWith P p
```

The existing module already has `@[expose] public section`. The helper becomes
public and receives a source/proof docstring; its proof is byte-for-byte unchanged.
The assigned module removes its duplicate and adds the private proof import
`Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence --uses
AlgebraicGeometry.AlgebraicSpace.representableWith_baseChange` found 54 downstream
modules; only the defining module currently mentions this previously private name.
All listed downstream modules retain their mathematical interfaces. Promotion adds
a proved theorem to their available API, and no definition changes meaning. The
new direct consumer is also listed below.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineStackStabilizerEtaleComparison` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceAmpleLocal` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen` | Y9 | Delete duplicate helper; privately import and use the existing one. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpacePushforwardAtlasEqualizer` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence` | unclaimed | Expose the existing helper; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.ClosedRelationSchematicNeighbourhood` | J1 | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.CommonMarkedNodalModel` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.DMIsomSpaceUnramified` | K1 | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleQuasiAffineImageScheme` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleSheafAlgebraicSpaceRealization` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleSheafSpaceAtlasBootstrap` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.InertiaFreeFiniteCoverCoarse` | S9 | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.NodalLogDualizingPullback` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.PlurinodalAlteration` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.PolarizedFineLogEtaleDescent` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.PolarizedSchemeEtaleDescent` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.QuasiprojectiveQCComposition` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.RepresentableFiniteStackProperties` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable` | W8 | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.SeparatingPairOpen` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.UniverseEnlargedEtaleRealization` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.AlgebraicGeometry.UnramifiedDiagonalEtaleAtlas` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.Paper.NormalLatticeFiniteCoverPresentation` | M6 | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.Paper.NormalProEtaleMonodromy` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.Paper.OrgogozoGoodModification` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.Paper.PlurinodalProperHypercover` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.Paper.TameIntegralReductionFamily` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.Paper.TraitNearbyBaseChange` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.SecPurity.NormalLocallyConstantFiniteSection` | S8 | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.TraceFormula.BoundedConstructibleTransport` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.TraceFormula.PsiProperSurjectiveConstructibility` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.TraceFormula.SchemeRelativeAmpleAffineCover` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.TraceFormula.SpaceSectionAlgebraEtaleBaseChange` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.TraceFormula.TemkinStableModification` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.TraceFormula.ValuationSemistableDominatesStable` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |
| `Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart` | unclaimed | No adaptation; existing signatures, proofs and public imports unchanged. |

## Status

landed 20261023T135748-L-2969913 2026-10-23 (merge of deliver/Y9/Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen)
