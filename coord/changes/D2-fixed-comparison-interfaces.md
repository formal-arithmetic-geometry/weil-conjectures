# perfectOverlapCompositeLocalIso

## Reason

Keep the existing real local-composite comparison behind no_expose and provide
its proved equation API. Its mathematical data and signature are unchanged.
Only the consumer explicitly unfolding its implementation is adapted.

## Old

```lean
noncomputable def perfectOverlapCompositeLocalIso
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (W : Y₀.Opens) :
    let hP : gf ⁻¹ᵁ W ≤ g ⁻¹ᵁ (f ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    derivedPullback (f ∣_ W) ⋙
      derivedPullback (g.resLE (f ⁻¹ᵁ W) (gf ⁻¹ᵁ W) hP) ≅
        derivedPullback (gf ∣_ W) := by
  intro hP
  have hcomp : g.resLE (f ⁻¹ᵁ W) (gf ⁻¹ᵁ W) hP ≫ (f ∣_ W) = gf ∣_ W := by
    apply (cancel_mono W.ι).1
    simp only [Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hgf]
  exact perfectHomComposition _ _ ≪≫
    eqToIso (congrArg (fun a ↦ derivedPullback a) hcomp)
```

## New

```lean
@[no_expose] noncomputable def perfectOverlapCompositeLocalIso
    {X Y Y₀ : Scheme.{u}} (f : Y ⟶ Y₀) (g : X ⟶ Y) (gf : X ⟶ Y₀)
    (hgf : g ≫ f = gf) (W : Y₀.Opens) :
    let hP : gf ⁻¹ᵁ W ≤ g ⁻¹ᵁ (f ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    derivedPullback (f ∣_ W) ⋙
      derivedPullback (g.resLE (f ⁻¹ᵁ W) (gf ⁻¹ᵁ W) hP) ≅
        derivedPullback (gf ∣_ W) := by
  intro hP
  have hcomp : g.resLE (f ⁻¹ᵁ W) (gf ⁻¹ᵁ W) hP ≫ (f ∣_ W) = gf ∣_ W := by
    apply (cancel_mono W.ι).1
    simp only [Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hgf]
  exact perfectHomComposition _ _ ≪≫
    eqToIso (congrArg (fun a ↦ derivedPullback a) hcomp)

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapOpenSquareCube | unclaimed | same data and signature |
| Sheaf.AlgebraicGeometry.PerfectOverlapRestrictedComposition | unclaimed | use the proved equation instead of unfolding |
| Sheaf.AlgebraicGeometry.PerfectOverlapCanonicalLocalCubeU | unclaimed | same data and signature |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeStageTail | unclaimed | same data and signature |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport | unclaimed | same data and signature |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeStageMap | unclaimed | same data and signature |
| Sheaf.AlgebraicGeometry.PerfectOverlapLocalSiteTriangle | unclaimed | same data and signature |
| Sheaf.AlgebraicGeometry.PerfectOverlapCanonicalGammaLocal | unclaimed | same data and signature |
| Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent | unclaimed | same data and signature |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeSiteComponent | D2 | same data and signature |
| Sheaf.AlgebraicGeometry.PerfectOverlapCanonicalOpenPrismU | unclaimed | same data and signature |
| Sheaf.AlgebraicGeometry.PerfectOverlapOpenPrismUOfData | unclaimed | same data and signature |

The original RestrictedComposition fails at line 42 with
`Tactic unfold failed to unfold perfectOverlapCompositeLocalIso`.
The change replaces that unfolding with the new equation API. The replacement
uses perfectOverlapCompositeLocalIso_eq, unfolds compositionTo and closes by reflexivity.
Existing unused-instance warnings are scoped off to preserve signatures; an unused
simp argument is removed. Dependent target meaning remains the same defining composite.

## Status

landed 20261016T095751-L-2157367 2026-10-16 (merge of deliver/D2/Sheaf.AlgebraicGeometry.PerfectOverlapCompositeSiteComponent)
