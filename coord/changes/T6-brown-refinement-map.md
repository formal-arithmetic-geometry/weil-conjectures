# AlgebraicGeometry.ProEtale.CondensedRing.brownCompactificationRefinementMap

## Reason

Share the existing canonical refinement component instead of reconstructing it with a
separate eqToHom. The two constructions have the same composite and differ only by
functor-category transport written as an object equality. Comparing their expanded
derived functor data exceeded the file compile limit. No mathematical map changes.
Mathlib `CategoryTheory.eqToHom_app` identifies
`(eqToIso h).hom.app K` with `eqToHom (Functor.congr_obj h K)`; proof
irrelevance identifies the two proofs of the resulting object equality. Thus
the transport factors in the old and new formulas are equal for every refinement
and every unbounded complex, with no extra hypothesis.

## Old

```lean
def brownCompactificationRefinementMap
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K ⟶
      (rightDerivedLowerShriekOfCompactification Λ d.obj.obj).obj K :=
  (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.map (localizingRefinementMap Λ r K) ≫
    (refinementDerivedLowerStarComp Λ r.hom.hom.hom c.obj.obj.g).inv.app
      ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K) ≫
    eqToHom (congrArg
      (fun q ↦ (lowerStar Λ q).rightDerivedFunctor.obj
        ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K))
      r.hom.hom.hom_g)

```

## New

```lean
def brownCompactificationRefinementMap
    {c d : Compactification.BoundaryCompactification f} (r : d ⟶ c)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K ⟶
      (rightDerivedLowerShriekOfCompactification Λ d.obj.obj).obj K :=
  compactificationRefinementComponent Λ r K

```

The coherence module becomes a public import because the definition now uses its
canonical component. Existing signatures and visibility stay identical. No target
statement uses this definition (the only textual consumer is the item theorem);
its mathematical meaning is preserved by the component equation above.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | Own proof uses the shared canonical map. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.Paper.MateOpenRestriction | D7 | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.Paper.ProperExceptionalRestriction | P2 | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.Paper.RationalExceptionalRestriction | K8 | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.Paper.RestrictionLocal | R3 | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.Paper.VerdierExchange | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.SecSmoothPurity.ReductionExceptional | F3 | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| TargetsCheck | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.TraceFormula.Statement | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No direct use of the changed definition; signatures and meaning unchanged. |

## Status

landed 20261019T112537-L-3953306 2026-10-19 (merge of deliver/T6/Sheaf.Paper.BrownExceptionalAdjoint)
