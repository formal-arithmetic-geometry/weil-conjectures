# SheafOfModules.sheafRingDerivedCoefficientAdjunction

## Reason

The retained proof introduces a private functor-presentation equality lemma preceded by
`omit [EssentiallySmall.{r} C] in` and
`set_option backward.isDefEq.respectTransparency false in`. Both commands apply to that
single private theorem. The preflight conservatively flags these added commands as an
interface change. This record documents their scope and the unchanged public contract.
No definition or existing statement changes, and no target needs semantic re-review.
The two new public helper theorems have their own new DAG nodes and are imported only
for proofs. No other group's module is edited.

## Old

The original public signature, verbatim:

```lean
theorem sheafRingDerivedCoefficientAdjunction (φ : O ⟶ O')
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))] :
    ∃ (_ : PreservesFiniteLimits (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)))
      (_ : PreservesFiniteColimits (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ))),
    ∀ (E : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O) ⥤
        SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))
      (h : ∀ M, E.obj M = changeOfRings φ M),
      (∀ {M N} (f : M ⟶ N), E.map f =
        eqToHom (h M) ≫ changeOfRingsHom φ M f ≫ eqToHom (h N).symm) →
      ∀ [E.Additive], ∃ a : E ⊣ restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ),
        (∀ (M : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))
          (N : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))
          (f : changeOfRings φ M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U),
          (a.homEquiv M N (eqToHom (h M) ≫ f)).val.app U x =
            f.val.app U
              ((CategoryTheory.toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
                ((1 : O'.obj.obj U) ⊗ₜ[O.obj.obj U, (φ.hom.app U).hom] x))) ∧
        ∀ (LF : DerivedCategory (SheafOfModules.{r}
            (derivedChangeRingIndependentCoefficients J O)) ⥤
            DerivedCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O')))
          (ε : DerivedCategory.Qh ⋙ LF ⟶
            E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
          LF.IsLeftDerivedFunctor ε
            (HomotopyCategory.quasiIso (SheafOfModules.{r}
              (derivedChangeRingIndependentCoefficients J O)) (ComplexShape.up ℤ)) →
          ∃ d : LF ⊣ (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategory,
            ∀ (P : CochainComplex (SheafOfModules.{r}
                (derivedChangeRingIndependentCoefficients J O)) ℤ),
              CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := O) P →
              (∀ i : ℤ, IsFlatOnSite (R := O) (P.X i)) →
              IsIso (ε.app ((HomotopyCategory.quotient _ _).obj P)) ∧
              (d.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
                  (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategory.map
                    (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≫
                  (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategoryFactorsh.hom.app
                    ((E.mapHomotopyCategory (ComplexShape.up ℤ)).obj
                      ((HomotopyCategory.quotient _ _).obj P)) =
                DerivedCategory.Qh.map
                  ((a.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
                    ((HomotopyCategory.quotient _ _).obj P))) ∧
              ∀ (H : HomotopyCategory (SheafOfModules.{r}
                  (derivedChangeRingIndependentCoefficients J O')) (ComplexShape.up ℤ))
                (g : (HomotopyCategory.quotient _ _).obj P ⟶
                  ((restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapHomotopyCategory (ComplexShape.up ℤ)).obj H),
                (d.homEquiv _ _).symm
                    (DerivedCategory.Qh.map g ≫
                      (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategoryFactorsh.inv.app H) =
                  ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
                    DerivedCategory.Qh.map
                      (((a.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv _ _).symm g) ∧
                ∀ [IsIso (DerivedCategory.Qh.map g)],
                  d.counit.app (DerivedCategory.Qh.obj H) =
                    inv (LF.map (DerivedCategory.Qh.map g ≫
                      (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategoryFactorsh.inv.app H)) ≫
                    ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
                    DerivedCategory.Qh.map
                      (((a.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv _ _).symm g)
```

The item had no private presentation-equality lemma and its proof was `by sorry`.

## New

The public signature is identical:

```lean
theorem sheafRingDerivedCoefficientAdjunction (φ : O ⟶ O')
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))]
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))] :
    ∃ (_ : PreservesFiniteLimits (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)))
      (_ : PreservesFiniteColimits (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ))),
    ∀ (E : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O) ⥤
        SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))
      (h : ∀ M, E.obj M = changeOfRings φ M),
      (∀ {M N} (f : M ⟶ N), E.map f =
        eqToHom (h M) ≫ changeOfRingsHom φ M f ≫ eqToHom (h N).symm) →
      ∀ [E.Additive], ∃ a : E ⊣ restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ),
        (∀ (M : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O))
          (N : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))
          (f : changeOfRings φ M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U),
          (a.homEquiv M N (eqToHom (h M) ≫ f)).val.app U x =
            f.val.app U
              ((CategoryTheory.toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
                ((1 : O'.obj.obj U) ⊗ₜ[O.obj.obj U, (φ.hom.app U).hom] x))) ∧
        ∀ (LF : DerivedCategory (SheafOfModules.{r}
            (derivedChangeRingIndependentCoefficients J O)) ⥤
            DerivedCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O')))
          (ε : DerivedCategory.Qh ⋙ LF ⟶
            E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
          LF.IsLeftDerivedFunctor ε
            (HomotopyCategory.quasiIso (SheafOfModules.{r}
              (derivedChangeRingIndependentCoefficients J O)) (ComplexShape.up ℤ)) →
          ∃ d : LF ⊣ (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategory,
            ∀ (P : CochainComplex (SheafOfModules.{r}
                (derivedChangeRingIndependentCoefficients J O)) ℤ),
              CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := O) P →
              (∀ i : ℤ, IsFlatOnSite (R := O) (P.X i)) →
              IsIso (ε.app ((HomotopyCategory.quotient _ _).obj P)) ∧
              (d.unit.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj P)) ≫
                  (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategory.map
                    (ε.app ((HomotopyCategory.quotient _ _).obj P)) ≫
                  (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategoryFactorsh.hom.app
                    ((E.mapHomotopyCategory (ComplexShape.up ℤ)).obj
                      ((HomotopyCategory.quotient _ _).obj P)) =
                DerivedCategory.Qh.map
                  ((a.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
                    ((HomotopyCategory.quotient _ _).obj P))) ∧
              ∀ (H : HomotopyCategory (SheafOfModules.{r}
                  (derivedChangeRingIndependentCoefficients J O')) (ComplexShape.up ℤ))
                (g : (HomotopyCategory.quotient _ _).obj P ⟶
                  ((restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapHomotopyCategory (ComplexShape.up ℤ)).obj H),
                (d.homEquiv _ _).symm
                    (DerivedCategory.Qh.map g ≫
                      (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategoryFactorsh.inv.app H) =
                  ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
                    DerivedCategory.Qh.map
                      (((a.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv _ _).symm g) ∧
                ∀ [IsIso (DerivedCategory.Qh.map g)],
                  d.counit.app (DerivedCategory.Qh.obj H) =
                    inv (LF.map (DerivedCategory.Qh.map g ≫
                      (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      φ)).mapDerivedCategoryFactorsh.inv.app H)) ≫
                    ε.app ((HomotopyCategory.quotient _ _).obj P) ≫
                    DerivedCategory.Qh.map
                      (((a.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv _ _).symm g)
```

The added scoped commands and their entire private declaration, verbatim:

```lean
omit [EssentiallySmall.{r} C] in
set_option backward.isDefEq.respectTransparency false in
private theorem coefficientPresentation_eq
    (φ : O ⟶ O')
    (E₀ E : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O) ⥤
      SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J O'))
    (h₀ : ∀ M, E₀.obj M = changeOfRings φ M)
    (h : ∀ M, E.obj M = changeOfRings φ M)
    (hm₀ : ∀ {M N} (f : M ⟶ N), E₀.map f =
      eqToHom (h₀ M) ≫ changeOfRingsHom φ M f ≫ eqToHom (h₀ N).symm)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ changeOfRingsHom φ M f ≫ eqToHom (h N).symm) : E₀ = E := by
  refine CategoryTheory.Functor.ext (fun M ↦ (h₀ M).trans (h M).symm) ?_
  intro M N f
  rw [hm₀, hm]
  simp
```

The second private helper transfers the existing K-flat comparison by uniqueness of
left derived functors; it adds no section command or public declaration. The completed
main proof is in the item module. All existing public imports, universes, section
variables, hypotheses and conclusions remain exactly as before.

## Users

`tools/downstream.py --uses sheafRingDerivedCoefficientAdjunction` reports the item and
five actual declaration users: ScalarInternalHomAdjunction, PointReductionUnits,
IntegralConstantCompletion, CoefficientEvaluationDerivedLeftAdjoint, and
ConstantRealizationDerivedScalarExtension. Their uses were read. All select the same
exactness witnesses, ordinary adjunction, or normalized derived adjunction from the
unchanged theorem signature. The table also lists every direct module importer, including
importers that never mention the declaration. The 1368 transitive module importers
inherit the same public signatures and public imports; no changed definition propagates.
Holders below were observed by the retained attempt; no consumer is edited by this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.ScalarInternalHomAdjunction | F3 | Uses the exactness witnesses via choose/choose_spec; unchanged signature and witnesses types. |
| Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction | S5 | Item: one proof closed; original public signature unchanged. |
| Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization | F9 | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.CategoryTheory.ScalarLocalizationDerivedHom | K4 | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.CategoryTheory.SystemLevelLeftExtension | M8 | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.ArbitraryFieldAdjunctionScalars | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint | P2 | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.CompletedMapReduction | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.ConstantRealizationDerivedScalarExtension | Z9 | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | U2 | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.FiniteFieldExceptionalPreservation | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.GeoCartierExponentIndependence | Y9 | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.IntegralLineTensorComparison | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.PbcScalarExtension | P9 | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.PointReductionUnitNormalization | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.PointReductionUnits | unclaimed | Uses the exactness witnesses via choose/choose_spec; all hypotheses, universes and witness types unchanged. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.ProperBaseChange.SingletonSiteModuleComparison | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.RingTheory.PseudoCoherentInverseRingReconstructionModels | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.SecSmoothPurity.OpenScalarExchange | S1 | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension | S8 | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | Z8 | No adaptation: public signatures and imports unchanged; proof-only scoped commands do not escape. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | not queried; unedited | Uses exactness and the derived adjunction; unchanged signature. |
| Sheaf.AlgebraicGeometry.ExcellentEtaleConstantProjection | not queried; unedited | Import only; unchanged public interface. |
| Sheaf.Paper.AdicExceptionalProjection | not queried; unedited | Import only; unchanged public interface. |
| Sheaf.RingTheory.CotangentFlatBaseChange | not queried; unedited | Import only; unchanged public interface. |

## Status

landed 20261019T093600-L-2330040 2026-10-19 (merge of deliver/S5/Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction)
