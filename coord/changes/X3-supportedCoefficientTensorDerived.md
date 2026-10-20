# AlgebraicGeometry.Etale.supportedCoefficientTensorDerived

## Reason

The previous concrete fibre-product specialization repeatedly unfolded the sheaf/complex
monoidal structures and exceeded the 60-second compiler limit. Generic comparison interfaces
and wrappers at a variable scheme share these structures before specialization. All seven
original proof obligations are now proved; none is weakened or moved to a new sorry.

The morphism types still denote the same signed tensor-complex and derived morphism families.
The complex map is now the actual totalization comparison rather than an existence witness;
`supportedSchemeComplexComparison_spec` proves its original bidegree characterization,
whose uniqueness identifies it with the former selected map. The derived condition retains
both naturality and the equation on every complex model, including the localization map
`μ ≫ Q.map (eqToHom ...)`. Its equality proof is the generic
`supportedComplexTensor_eq`, which is the same identification as
`supportedComplexTensorGeneric_eq` by proof irrelevance. The family evaluation wrapper is
definitionally evaluation of the selected unique family.

No Challenge statement is edited. Because these definitions lie below the targets, their
meaning is submitted again for the independent stage-2 check; the intended supported product
and all hypotheses and conclusions are unchanged. No source-library file is changed.

## Old

```lean
noncomputable def supportedCoefficientTensorDerived
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
      (supportedCoefficients A (supportedProductImmersion f g i j)).mapDerivedCategory.obj
          (M ⊗ N) ⟶
        ((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).obj
          ((supportedFirstCoefficients A f g i).mapDerivedCategory.obj M)).obj
          ((supportedSecondCoefficients A f g j).mapDerivedCategory.obj N) :=
  (exists_unique_supportedCoefficientTensorDerived A f g i j).choose M N
```

## New

```lean
noncomputable def supportedCoefficientTensorDerived
    (A : Type (u + 1)) [CommRing A] {B X Y Z W : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
      (supportedCoefficients A (supportedProductImmersion f g i j)).mapDerivedCategory.obj
          (M ⊗ N) ⟶
        ((derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).obj
          ((supportedFirstCoefficients A f g i).mapDerivedCategory.obj M)).obj
          ((supportedSecondCoefficients A f g j).mapDerivedCategory.obj N) :=
  supportedSchemeDerivedApply (ModuleCat.{u + 1} A) (pullback f g)
    (supportedCoefficients A (supportedProductImmersion f g i j))
    (supportedFirstCoefficients A f g i) (supportedSecondCoefficients A f g j)
    (exists_unique_supportedCoefficientTensorDerived A f g i j).choose M N
```

## Users

`tools/downstream.py --uses supportedCoefficientTensorDerived` was checked, together with qualified uses.
There are 66 transitive import consumers. The direct textual users are below; all retain
the same mathematical statements.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedExteriorProduct | X3 | Uses the same normalized signed comparison through the smaller interface. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct | W4 | Textual matches refer to its own ProEtale namespace; its imported Etale interface and meaning stay the same. No edits. |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | P7 | Uses the comparison and the naturality conjunct of its uniqueness theorem; the family and naturality equation are unchanged. No edits. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Composes the comparison with pullback evaluations. Its morphism type and canonical comparison are unchanged. No edits. |

## Status

landed 20261020T211856-L-3513030 2026-10-20 (merge of deliver/X3/Sheaf.AlgebraicGeometry.SupportedExteriorProduct)
