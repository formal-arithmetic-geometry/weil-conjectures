# Sheaf.Paper.CoefficientDerivedFunctorAPI restoration

## Reason

The assigned rework row records the removal of this module after a cluster restore.
Restore the complete archived API to its original Lean path. Its absence prevents
restoration of the coefficient comparison consumers that still depend on its node.
The archive itself compiles against the current library. Preserve all its definitions,
public imports, attributes and signatures. Rewrite the two component proofs using
coefficientAmbientSquare_eq, retaining the objectwise construction behind no_expose.
No arbitrary witness is chosen and no mathematical definition or statement changes.

## Old

The live module is absent. The baseline is the complete preserved source at
quarantine/Sheaf/Paper/CoefficientDerivedFunctorAPI.lean, identified by coord/rework.tsv.
Its ambient-square construction is:

```lean
/-- The ambient derived pullback comparison, before restricting to constructible objects. -/
@[no_expose, irreducible] noncomputable def coefficientAmbientSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    coefficientDerivedUpperStar Λ g ⋙
        coefficientDerivedUpperStar Λ f' ≅
      coefficientDerivedUpperStar Λ f ⋙
        coefficientDerivedUpperStar Λ g' :=
  coefficientIsoTransThree (coefficientDerivedUpperStarComp Λ f' g).symm
    (eqToIso (congrArg (coefficientDerivedUpperStar Λ) sq.w.symm))
    (coefficientDerivedUpperStarComp Λ g' f)
```

## New

Restore every archived declaration, including the same ambient-square definition:

```lean
/-- The ambient derived pullback comparison, before restricting to constructible objects. -/
@[no_expose, irreducible] noncomputable def coefficientAmbientSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    coefficientDerivedUpperStar Λ g ⋙
        coefficientDerivedUpperStar Λ f' ≅
      coefficientDerivedUpperStar Λ f ⋙
        coefficientDerivedUpperStar Λ g' :=
  coefficientIsoTransThree (coefficientDerivedUpperStarComp Λ f' g).symm
    (eqToIso (congrArg (coefficientDerivedUpperStar Λ) sq.w.symm))
    (coefficientDerivedUpperStarComp Λ g' f)
```

Both archived public imports remain public. The only changes relative to the archive
are theorem proofs: coefficientAmbientSquare_app rewrites coefficientAmbientSquare_eq
and checks its objectwise components; coefficientAmbientSquare_hom_app rewrites the
same equation and applies coefficientIsoTransThree_hom_app. Definition bodies,
visibility, theorem signatures and instance scope remain identical. No consumer
adaptation or target semantic review is required.

## Users

The source-only downstream query, with --allow-missing, reports zero live importers.
That does not authorize withdrawal: the following quarantined textual consumers and
their DAG dependencies remain. No consumer file is changed by this packet.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed in shared snapshot | Archived source retained; all API signatures and bodies preserved. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed in shared snapshot | Archived source retained; all API signatures and bodies preserved. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed in shared snapshot | Archived source retained; all API signatures and bodies preserved. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed in shared snapshot | Archived source retained; all API signatures and bodies preserved. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed in shared snapshot | Archived source retained; all API signatures and bodies preserved. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed in shared snapshot | Archived source retained; all API signatures and bodies preserved. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed in shared snapshot | Archived source retained; all API signatures and bodies preserved. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed in shared snapshot | Archived source retained; all API signatures and bodies preserved. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed in shared snapshot | Archived source retained; all API signatures and bodies preserved. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed in shared snapshot | Archived source retained; all API signatures and bodies preserved. |

An isolated importing-module check compiles the ambient_square_eq proof from
FiniteDiscreteCoefficientSquareCoherence unchanged, and its etale_square_eq proof
with the obsolete pullbackSquareComparison_def rewrite replaced by unfolding the
now-exposed upstream definition, using only the restored public import. This checks visibility of the named local instance,
the cached composition and square interfaces, and the defining-equation APIs.

## Status

landed 20261021T021923-L-2793030 2026-10-21 (merge of deliver/P3/Sheaf.Paper.CoefficientDerivedFunctorAPI)
