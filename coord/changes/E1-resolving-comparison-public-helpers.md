# RingedKFlatWord.comparison_descent_iso visibility

## Reason

The item proof uses the existing unique comparison descent theorem from the word-comparison
module. Its declaration was private, so the proof could not reference it across modules. The
proof body and signature are unchanged; only visibility is exposed. The source module is
unclaimed.

## Old

```lean
private theorem comparison_descent_iso
    {B₀ : Type*} [Category B₀] [Abelian B₀] [HasDerivedCategory B₀]
    {D₀ : Type*} [Category D₀]
    (res : CochainComplex B₀ ℤ → Prop)
    (hres : ∀ K, ∃ (P : CochainComplex B₀ ℤ) (p : P ⟶ K), QuasiIso p ∧ res P)
    (F G : DerivedCategory B₀ ⥤ D₀) (U V : CochainComplex B₀ ℤ ⥤ D₀)
    (εF : DerivedCategory.Q ⋙ F ⟶ U) (εG : DerivedCategory.Q ⋙ G ⟶ V)
    (hF : ∀ P, res P → IsIso (εF.app P))
    (hG : ∀ P, res P → IsIso (εG.app P)) (t : U ≅ V) :
    ∃! τ : F ≅ G, ∀ P, res P → τ.hom.app (DerivedCategory.Q.obj P) ≫ εG.app P =
      εF.app P ≫ t.hom.app P
```

## New

```lean
theorem comparison_descent_iso
    {B₀ : Type*} [Category B₀] [Abelian B₀] [HasDerivedCategory B₀]
    {D₀ : Type*} [Category D₀]
    (res : CochainComplex B₀ ℤ → Prop)
    (hres : ∀ K, ∃ (P : CochainComplex B₀ ℤ) (p : P ⟶ K), QuasiIso p ∧ res P)
    (F G : DerivedCategory B₀ ⥤ D₀) (U V : CochainComplex B₀ ℤ ⥤ D₀)
    (εF : DerivedCategory.Q ⋙ F ⟶ U) (εG : DerivedCategory.Q ⋙ G ⟶ V)
    (hF : ∀ P, res P → IsIso (εF.app P))
    (hG : ∀ P, res P → IsIso (εG.app P)) (t : U ≅ V) :
    ∃! τ : F ≅ G, ∀ P, res P → τ.hom.app (DerivedCategory.Q.obj P) ≫ εG.app P =
      εF.app P ≫ t.hom.app P
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent | unclaimed | Existing internal uses remain unchanged. |
| Sheaf.Paper.FiniteDerivedComparisonNormalization | E1 | Uses the theorem in composition descent. |

## Status

landed 20261025T204517-L-2965299 2026-10-25 (merge of deliver/E1/Sheaf.Paper.FiniteDerivedComparisonNormalization)
