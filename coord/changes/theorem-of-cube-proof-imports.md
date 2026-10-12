# WeilConjectures.AlgebraicGeometry.TheoremOfCube proof-only imports

## Reason

Second reading found that GlobalSectionsBijective and Modules.Rigidification are used only
by proofs, not by existing declaration signatures or by preimageSnd. Stage-3 import rules
require these to be plain imports. This changes import visibility, so the preflight requires
a change record even though no mathematical statement or definition changes.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Modules.Rigidification
```

## New

```lean
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.Modules.Rigidification
```

## Users

Ran tools/downstream.py for the cube module with uses GlobalSectionsBijective,
exists_isFreeGenerator_top_of_comp_eq_id, isIso_app_of_isPullback, and
bijective_app_of_comp_eq_id. It lists 129 downstream modules. The latter three names
occur only in the item itself. The GlobalSectionsBijective textual hits are the item,
WeilConjectures, Curve.Affine, and Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange;
the latter three retain their public import paths. Read both direct importers:
AbelianVariety.Cube uses the retained cube API, not these proof helpers; the umbrella
WeilConjectures directly imports both modules. Checked import closure for every
transitive downstream module. No declaration, definition, target meaning or statement
changes. The six abelian-variety modules whose public closure loses GlobalSectionsBijective
are also compiled from unchanged scratch copies in dependency order against this delivery.
No module besides the item needs adaptation; existing claims are untouched.

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | S2 | Proof imports retained privately; all existing statements and definitions identical. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | U2 | Both modules accessible through other import paths; no statement or proof adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| TargetsCheck | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | none | Unchanged source checked by single-file compilation in import order against corrected cube; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | none | Unchanged source checked by single-file compilation in import order against corrected cube; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | none | Unchanged source checked by single-file compilation in import order against corrected cube; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | none | Unchanged source checked by single-file compilation in import order against corrected cube; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | none | Unchanged source checked by single-file compilation in import order against corrected cube; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | none | Unchanged source checked by single-file compilation in import order against corrected cube; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | H1 | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.FourierTransform.AffineSpace | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.FourierTransform.Defs | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.FourierTransform.Inversion | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.FourierTransform.Perverse | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.FourierTransform.Properties | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.FourierTransform.Properties.BaseChange | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.FourierTransform.Properties.Stalk | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | none | Both modules accessible through other import paths; no statement or proof adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | none | No statement meaning change; imports the retained cube API; no textual use of removed proof helpers. |

## Status

landed 20261012T053954-L-2645949 2026-10-12 (merge of deliver/S2/WeilConjectures.AlgebraicGeometry.TheoremOfCube)
