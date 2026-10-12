# generic_fibre_component_spread_trace / generic_fibre_component_spread_trace_reverse

## Reason

STATEMENT-DISPUTED (original forward statement): choose `A = ∅`. The hypotheses hold,
but `x` belongs to its fibre component and cannot belong to the empty trace.
STATEMENT-DISPUTED (original reverse statement): take `T = Spec k` and `P` the disjoint
union of two copies of `Spec k`, with its finite structure morphism, `V = T`, `A = P`.
The trace is clopen but contains both components; the component through `x` contains one.

The repaired inclusions require `x ∈ A`, and the reverse inclusion also requires
preconnectedness of the fibre trace. These are proved from Mathlib, without any sorry.
No target statement or definition changes. Their sole direct caller still states the
same geometric existence theorem, but its proof must be reopened: the current core
returns `V = univ`, `A = univ` and supplies no preconnectedness. The old proof falsely
identified every clopen trace with the component. The named geometric obligation and
its complete source proof already exist at `lem-sbc-generic-fibre-component-spread`.

## Old

```lean
theorem generic_fibre_component_spread_trace {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (x : P) (hx : g x = y)
    (V : Set T) (A : Set P)
    (hV : IsOpen V) (hy : y ∈ V)
    (hcl : IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A}) :
    connectedComponentIn (g ⁻¹' {y}) x ⊆ g ⁻¹' {y} ∩ A

theorem generic_fibre_component_spread_trace_reverse {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (x : P) (hx : g x = y)
    (V : Set T) (A : Set P)
    (hV : IsOpen V) (hy : y ∈ V)
    (hcl : IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A}) :
    g ⁻¹' {y} ∩ A ⊆ connectedComponentIn (g ⁻¹' {y}) x

```

## New

```lean
theorem generic_fibre_component_spread_trace {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (x : P) (hx : g x = y)
    (V : Set T) (A : Set P)
    (hV : IsOpen V) (hy : y ∈ V)
    (hcl : IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A})
    (hxA : x ∈ A) :
    connectedComponentIn (g ⁻¹' {y}) x ⊆ g ⁻¹' {y} ∩ A

theorem generic_fibre_component_spread_trace_reverse {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (x : P) (hx : g x = y)
    (V : Set T) (A : Set P)
    (hV : IsOpen V) (hy : y ∈ V)
    (hcl : IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A})
    (hxA : x ∈ A) (hconn : IsPreconnected (g ⁻¹' {y} ∩ A)) :
    g ⁻¹' {y} ∩ A ⊆ connectedComponentIn (g ⁻¹' {y}) x

```

## Users

Only `Sheaf.AlgebraicGeometry.GenericFibreComponentSpread` calls the changed declarations.
Its sole theorem signature and all visibility are identical. The forced edit replaces
its proof body (lines 50–55) by `by sorry`, because the old applications now produce
functions awaiting missing hypotheses, instead of proofs of the inclusions. No other
lines of that module change. Imports are retained to obey the minimal adaptation rule.
All other users import this unchanged geometric existence interface transitively.
Their statements and definitions therefore have the same meaning, including targets.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.GenericFibreComponentSpread | unclaimed | forced proof reopening; signature unchanged |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | transitive only; signature and meaning unchanged |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | transitive only; signature and meaning unchanged |
| TargetsCheck | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.FourierTransform.Defs | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.FourierTransform.Inversion | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.FourierTransform.Perverse | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.FourierTransform.Properties | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | transitive only; signature and meaning unchanged |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | transitive only; signature and meaning unchanged |

## Status

landed 20261012T213855-L-1210466 2026-10-12 (merge of deliver/W3/Sheaf.AlgebraicGeometry.GenericFibreComponentSpreadTrace)
