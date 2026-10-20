# AlgebraicGeometry.Scheme.PositiveNat

## Reason

Retirement item in coord/retire-items.tsv, under the human-approved hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The Sheaf module only re-exports the
upstream torsion-sheaf construction and supplies an alias of its actual index.
Use the original index and positivity theorem directly and withdraw the wrapper.

## Old

```lean
module

public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf

@[expose] public section

namespace AlgebraicGeometry.Scheme

/-- Positive integers with the divisibility order, the canonical torsion-filtration index. -/
abbrev PositiveNat := PNat.DvdOrder

/-- Positivity of the torsion-filtration index. -/
theorem PositiveNat.pos (n : PositiveNat) : 0 < n.val := PNat.DvdOrder.val_pos n

end AlgebraicGeometry.Scheme
```

## New

Withdraw lean/Sheaf/AlgebraicGeometry/TorsionEtaleSheaf.lean using deleted.txt.
Every direct consumer imports WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
with the same public/private visibility as before. Replace PositiveNat by its
verbatim abbreviation body PNat.DvdOrder, and each use of its positivity lemma
by PNat.DvdOrder.val_pos. No new declaration replaces the compatibility names.
The public fieldInvertibleTorsionDiagram signature expands this abbreviation;
its elaborated type and the diagram, cocone and comparison remain identical.
The DAG definition attachment moves to the upstream module, existing: true.
No upstream file or target statement changes. The torsion predicate already
came from the upstream module before this retirement, so no target semantics
change and no target-definition review is reopened.

## Users

The direct-import scan currently finds 11 consumers (the queue snapshot listed
20). The following table also covers all current transitive import consumers.
A full-library textual scan finds PositiveNat only in the withdrawn module,
InvertibleOrdersColimit and TorsionFilteredUnion. These two consumers are the
only places needing API adaptations. All changed direct consumers are unclaimed.
The diagram's downstream users keep the same definitionally equal type.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Replace only the import with the upstream twin; declarations and proofs identical. |
| Sheaf.AlgebraicGeometry.ArtinTensorEtaleAcyclic | unclaimed | Replace only the import with the upstream twin; declarations and proofs identical. |
| Sheaf.AlgebraicGeometry.ConstructibleCurveAnnihilator | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.ConstructibleCurveQuotPart | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.ConstructibleCurveSubPart | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.ConstructibleCurveSubQuotient | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.ConstructibleIntegralCoefficientsBackward | unclaimed | Replace only the import with the upstream twin; declarations and proofs identical. |
| Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.ConstructibleTorsionModulesAgree | unclaimed | Replace only the import with the upstream twin; declarations and proofs identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralBoundaryFiniteness | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferRetract | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardCoefficientControl | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardCohomologyComparison | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardPullbackComparison | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.Curve.RetractAssertions | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.CurveCoefficientPair | unclaimed | Replace only the import with the upstream twin; declarations and proofs identical. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.InvertibleOrdersColimit | unclaimed | Import upstream twin; expand the definitionally equal index alias and use val_pos. |
| Sheaf.AlgebraicGeometry.PrimeInjectiveAcyclicityOfBaseChange | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.ProjectiveStrictLocalIntersectionAcyclic | unclaimed | Replace only the import with the upstream twin; declarations and proofs identical. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | Q5 | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound | unclaimed | Replace only the import with the upstream twin; declarations and proofs identical. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeModN | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChange | unclaimed | Replace only the import with the upstream twin; declarations and proofs identical. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Replace only the import with the upstream twin; declarations and proofs identical. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Import upstream twin; use DvdOrder and val_pos in the existing proof. |
| Sheaf.Paper.CompactSupportStaircaseExpansion | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.Paper.DeltaRestriction | X9 | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.Paper.ProperOpenRefinementAdjointProjection | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.Paper.ProperOpenTowerDerivedUnit | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.Paper.UnboundedProperOpenInterchange | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | No source change; no compatibility-name use; underlying torsion construction identical. |

## Status

landed 20261020T141320-L-2036858 2026-10-20 (merge of deliver/X3/Sheaf.AlgebraicGeometry.TorsionEtaleSheaf)
