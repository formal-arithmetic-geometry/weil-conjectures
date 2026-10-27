# Sheaf.Paper.ClosedAdjointConstructibleYoneda coefficient transport proof

## Reason

Repair the return at 1362f3092, whose Lean module was already byte-identical to the
current library. The retained proof depended directly on private lemmas of
`IntegralConstantModelHeartClosure` for a general coefficient-isomorphism argument.
Use the general finite-constant-model transport lemmas of
`CondensedCoefficientIsoConstructible` instead. Prove reflection by applying forward
transport along the inverse coefficient map, then cancel the two restrictions with
`Mod.comapComp` and `Mod.comapId`. This removes the direct integral-heart dependency
while preserving the complete Yoneda proof and every public declaration.

This delivery is relative to the current library. It does not restore an absent
module or change the coefficient convention: those edits are already present there.
The item's actual direct hole count is zero before and after this repair.

## Old

```lean
import all Sheaf.Paper.IntegralConstantModelHeartClosure
```

The private theorem `bounded_comap_iff` used `constantModel_comap_iff` and
`constructible_iso` from that module. Its signature and the public theorem's
signature are unchanged by this repair.

## New

```lean
import all Sheaf.Paper.CondensedCoefficientIsoConstructible
```

The private theorem `bounded_comap_iff` proves its heart-level equivalence locally
from `constructible_comap` in the two directions and the composite-restriction
isomorphism. It then applies the same exact homology comparison as before, using
`constructible_iso` from the general coefficient-transport module. No new public
API, definition, unproved lemma or theorem hypothesis is introduced.

## Users

The table lists all current transitive consumers from `tools/downstream.py`, plus
the item. Searching those consumers with `--uses closedAdjointConstructibleYoneda`
finds only the declaration itself. This is a private proof-import change: every
public import and declaration signature is identical to the current library, so
none of these consumers needs an adaptation. The removed module remains in the
transitive import closure through other dependencies; no global pruning is claimed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | E2 | Private coefficient-transport proof repaired; theorem type unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| TargetsCheck | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Public signatures and public imports unchanged; no adaptation needed. |

## Status

landed 20261022T143134-L-972067 2026-10-22 (merge of deliver/E2/Sheaf.Paper.ClosedAdjointConstructibleYoneda)
