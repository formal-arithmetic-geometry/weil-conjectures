# AlgebraicGeometry.formalFunctions_degreeZero_compatibility

## Reason

The old universal formula for arbitrary a and b is false. For f = id on Spec Q,
canonical degree-zero theta and t = 1, canonical identifications give 1. Replacing
b by its composite with multiplication by -1 is another inverse-system
isomorphism, but makes the formula read -1 = 1. IsFormalFunctionsTheta constrains
neither a nor b. The intermediate theorem must instead choose the identifications
jointly and identifies the underlying map of a with the canonical augmentation.
This is stronger than the dictionary, rather than its duplicate. The parent now constructs a from the augmentation and reduces the fibre
system and germ formula to a strictly smaller named obligation.

## Old

```lean
theorem formalFunctions_degreeZero_compatibility {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y)
    (a : ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))) ≃ₗ[
          Y.presheaf.stalk y]
        formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0)
    (b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ≅
          formalFibreSectionsSystem f y) :
    ∀ (n : ℕ)
      (θ : formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0 →ₗ[
        Y.presheaf.stalk y]
        formalFibreCohomologyLocal f y (SheafOfModules.unit X.ringCatSheaf) 0 n),
      IsFormalFunctionsTheta f y (SheafOfModules.unit X.ringCatSheaf) 0 n θ →
      ∀ (V : Y.Opens) (hy : y ∈ V)
        (hV : (⊤ : (formalFibre f y n).Opens) ≤
          (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) (t : Γ(X, f ⁻¹ᵁ V)),
        (b.hom.app (op n)) (θ (a (TopCat.Presheaf.germ
          ((Scheme.Modules.pushforward f).obj
            (SheafOfModules.unit X.ringCatSheaf)).val.presheaf V y hy t))) =
          (formalFibreι f y n).appLE (f ⁻¹ᵁ V) ⊤ hV t
```

## New

```lean
theorem formalFunctions_degreeZero_compatibility {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) :
    ∃ a : ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))) ≃ₗ[
          Y.presheaf.stalk y]
        formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0,
      a.toLinearMap = ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map
        ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).toRightDerivedZero.app
          (SheafOfModules.unit X.ringCatSheaf))).hom ∧
      ∃ b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ≅
          formalFibreSectionsSystem f y,
        ∀ (n : ℕ)
          (θ : formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0 →ₗ[
            Y.presheaf.stalk y]
            formalFibreCohomologyLocal f y (SheafOfModules.unit X.ringCatSheaf) 0 n),
          IsFormalFunctionsTheta f y (SheafOfModules.unit X.ringCatSheaf) 0 n θ →
          ∀ (V : Y.Opens) (hy : y ∈ V)
            (hV : (⊤ : (formalFibre f y n).Opens) ≤
              (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) (t : Γ(X, f ⁻¹ᵁ V)),
            (b.hom.app (op n)) (θ (a (TopCat.Presheaf.germ
              ((Scheme.Modules.pushforward f).obj
                (SheafOfModules.unit X.ringCatSheaf)).val.presheaf V y hy t))) =
              (formalFibreι f y n).appLE (f ⁻¹ᵁ V) ⊤ hV t
```

The public import of FormalFunctionsDegreeZeroStalkIso is replaced by
FormalFibreCohomology, which supplies the signature's definitions. No statement
or definition of Challenge.lean changes. The dictionary signature is identical;
only its now-invalid application is replaced by extracting the joint witnesses
and discarding the additional canonical-map equality.
The new augmentation compatibility theorem is stronger than an arbitrary choice
of stalk equivalence: its stalk map is the fixed canonical augmentation. The
parent proves that map bijective; there is no data chosen from a sorry theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroDictionary | unclaimed | Its signature and visibility stay identical. The old application to a and b fails after the correction, so the three proof lines are replaced by extracting the canonical witnesses and discarding their additional augmentation equality. Its original imports remain: unrelated pruning in this unheld adaptation is forbidden. |
| Sheaf.AlgebraicGeometry.FormalFunctionsStalk | unclaimed | It uses the unchanged dictionary statement; no source adaptation or meaning change. |

The baseline DAG has no citer of the changed compatibility node, even though the
Lean dictionary imports and applies it. Its dependency record is repaired here;
the dictionary still holds with the forced proof adaptation. The
unit sk-thm-p1 and its realized statement and steps are unchanged. Downstream
target meaning is unchanged, since this delivery changes no definition.

## Status

landed 20261012T194139-L-464476 2026-10-12 (merge of deliver/S2/Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroCompatibility)
