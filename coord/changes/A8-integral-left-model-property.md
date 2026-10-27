# integralTensorLeftModelProperty

## Reason

Factor the canonical first-slot normalization through abstract model data.
This freezes the coefficient category, tower, quotient and completed tensor functors
during the proof;
repeatedly converting their concrete maps otherwise expands large constructions.
The canonical predicate specializes this definition to the original data.
This is a new generic definition realizing the existing shift-properties node,
not a new proof obligation. It contains no postponed data or proof.

## Old

No prior declaration.

## New

```lean
def integralTensorLeftModelProperty {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] (r : ℤ) (Good : ObjectProperty (CochainComplex A ℤ))
    (T : CochainComplex A ℤ × CochainComplex A ℤ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (Φ : ∀ P Q : CochainComplex A ℤ,
      (T.obj (P⟦r⟧, Q) ≅ T.obj (P, Q) ⋙ shiftFunctor (CochainComplex A ℤ) r) → Prop)
    {D : Type c} [Category.{d} D] (F : CochainComplex A ℤ ⥤ D) (S : D ⥤ D)
    (γ : shiftFunctor (CochainComplex A ℤ) r ⋙ F ≅ F ⋙ S) (G : D × D ⥤ D)
    (ε : ((Good.ι ⋙ F).prod (Good.ι ⋙ F)) ⋙ G ≅
      (Good.ι.prod Good.ι) ⋙ (T ⋙ integralOperationsRoosFunctor) ⋙ F)
    (σ : S.prod (𝟭 D) ⋙ G ≅ G ⋙ S) : Prop :=
  ∀ (P Q : Good.FullSubcategory),
    ∃ (hP : Good (P.obj⟦r⟧))
      (α : T.obj (P.obj⟦r⟧, Q.obj) ≅
        T.obj (P.obj, Q.obj) ⋙
          shiftFunctor (CochainComplex (A) ℤ) r),
      Φ P.obj Q.obj α ∧
      ∃ (δ : CochainComplex.mappingCone (completedTensorShiftOneSub
            (T.obj (P.obj⟦r⟧, Q.obj))) ≅
          (CochainComplex.mappingCone (completedTensorShiftOneSub
            (T.obj (P.obj, Q.obj))))⟦r⟧),
        completedTensorShiftConeFormula
            (T.obj (P.obj, Q.obj))
            (T.obj (P.obj⟦r⟧, Q.obj)) r α δ ∧
        G.map
            ((γ.hom.app P.obj),
              𝟙 (F.obj Q.obj)) ≫
          σ.hom.app (F.obj P.obj, F.obj Q.obj) ≫
          S.map
            (ε.hom.app (P, Q)) =
        ε.hom.app (⟨P.obj⟦r⟧, hP⟩, Q) ≫
          F.map
            (completedTensorShiftRoosIso
              (T.obj (P.obj, Q.obj))
              (T.obj (P.obj⟦r⟧, Q.obj)) r δ).hom ≫
          γ.hom.app
            ((T ⋙ integralOperationsRoosFunctor).obj (P.obj, Q.obj))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralTensorShiftProperties | unclaimed | Canonical predicate is the definitionally identical specialization. |
| Sheaf.SixFunctors.IntegralTensorLeftShiftUnique | A8 | Proves normalization with abstract model data, then specializes once. |

The existing canonical predicate keeps its complete original signature. Its
meaning, and hence every affected target's meaning, is unchanged. The exact old
formula is checked against the new specialization by `Iff.rfl` in a mirrored
consumer tree. That check compiled successfully against the patched dependency. All three current direct consumers compiled unchanged against the patched dependency.
This change reopens meaning review under AGENTS.md §4; the old and new canonical
definitions are recorded in A8-integral-left-property-reducibility.md.

## Status

landed 20261026T022806-L-446879 2026-10-26 (merge of deliver/A8/Sheaf.SixFunctors.IntegralTensorLeftShiftUnique)
