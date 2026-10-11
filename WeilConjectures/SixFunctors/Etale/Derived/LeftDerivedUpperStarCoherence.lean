/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
public import WeilConjectures.SixFunctors.BaseChange.Pasting
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Coherence of the composition isomorphisms of the derived pullback

The composition isomorphisms `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`) of the derived pullbacks of étale sheaves
are compatible with the counits `Qh ⋙ Lg^* ⟶ g^* ⋙ Qh` of the left derived functors, and they
satisfy the associativity law of a pseudofunctor: for `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ W`,
the two identifications `L(fgh)^* ≅ Lh^* ⋙ Lg^* ⋙ Lf^*` agree.

## Main statements

- `AlgebraicGeometry.Etale.leftDerivedUpperStarComp_hom_app_comp_counit`: compatibility with
  the counits.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarComp_assoc`: the associativity law.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

lemma mapHomotopyCategoryCompIso_inv_app_quotient {V W W' : Type*} [Category V] [Category W]
    [Category W'] [Preadditive V] [Preadditive W] [Preadditive W'] {ι : Type*}
    {c : ComplexShape ι} {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] (K : HomologicalComplex V c) :
    (Functor.mapHomotopyCategoryCompIso e c).inv.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient W' c).map
        ((Functor.mapHomologicalComplexCompIso e c).inv.app K) :=
  rfl

lemma mapHomotopyCategory_app_quotient {V W : Type*} [Category V] [Category W]
    [Preadditive V] [Preadditive W] {ι : Type*} {c : ComplexShape ι} {F G : V ⥤ W}
    [F.Additive] [G.Additive] (α : F ⟶ G) (K : HomologicalComplex V c) :
    (NatTrans.mapHomotopyCategory α c).app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient W c).map ((NatTrans.mapHomologicalComplex α c).app K) :=
  rfl

/-- The composition isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` is compatible with the counits
of the derived pullbacks: on a complex `K`, its composite with the counits is the counit of
`L(g₁ ≫ g₂)^*` followed by the composition isomorphism `(g₁ ≫ g₂)^* ≅ g₂^* ⋙ g₁^*` of the
underived pullbacks, applied levelwise. -/
@[reassoc]
lemma leftDerivedUpperStarComp_hom_app_comp_counit {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (h : g₁₂ = g₁ ≫ g₂)
    (K : HomotopyCategory (Sheaf R.smallEtaleTopology A) (ComplexShape.up ℤ)) :
    (leftDerivedUpperStarComp A g₁ g₂ g₁₂ h).hom.app (DerivedCategory.Qh.obj K) ≫
        (L((g₁)^*[A])).map ((g₂)^*[A].leftDerivedFunctorCounit.app K) ≫
          (g₁)^*[A].leftDerivedFunctorCounit.app
            (((g₂)^*[A].mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
      (g₁₂)^*[A].leftDerivedFunctorCounit.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          (Etale.upperStarComp A g₁ g₂ g₁₂ h).hom (ComplexShape.up ℤ)).app K ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl ((g₂)^*[A] ⋙ (g₁)^*[A]))
            (ComplexShape.up ℤ)).inv.app K) := by
  simp only [leftDerivedUpperStarComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Functor.leftDerivedFunctorCompIso_hom_app_comp_counit,
    Functor.leftDerivedFunctorNatIso_hom_app_comp_counit_assoc, Functor.map_comp]

/-- The associativity law of the composition isomorphisms of the derived pullbacks: for
`f : X ⟶ Y`, `g : Y ⟶ Z` and `h : Z ⟶ W`, the two identifications
`L(fgh)^* ≅ Lh^* ⋙ Lg^* ⋙ Lf^*` agree.
```
L(fgh)^* ───────────▶ Lh^* ⋙ L(fg)^*
    │                        │
    ▼                        ▼
L(gh)^* ⋙ Lf^* ──────▶ Lh^* ⋙ Lg^* ⋙ Lf^*
``` -/
lemma leftDerivedUpperStarComp_assoc {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ W) (fg : X ⟶ Z) (gh : Y ⟶ W) (fgh : X ⟶ W) (hfg : fg = f ≫ g) (hgh : gh = g ≫ h)
    (hfgh : fgh = fg ≫ h) :
    (leftDerivedUpperStarComp A fg h fgh hfgh).hom ≫
        Functor.whiskerLeft (L((h)^*[A])) (leftDerivedUpperStarComp A f g fg hfg).hom =
      (leftDerivedUpperStarComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
        Functor.whiskerRight (leftDerivedUpperStarComp A g h gh hgh).hom (L((f)^*[A])) := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf W.smallEtaleTopology A) (ComplexShape.up ℤ)) fun K ↦ ?_
  let κ := (L((f)^*[A])).map ((L((g)^*[A])).map ((h)^*[A].leftDerivedFunctorCounit.app K)) ≫
    (L((f)^*[A])).map ((g)^*[A].leftDerivedFunctorCounit.app
      (((h)^*[A].mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≫
    (f)^*[A].leftDerivedFunctorCounit.app (((g)^*[A].mapHomotopyCategory (ComplexShape.up ℤ)).obj
      (((h)^*[A].mapHomotopyCategory (ComplexShape.up ℤ)).obj K))
  have : IsIso κ := by dsimp only [κ]; infer_instance
  rw [← cancel_mono κ]
  have hc₁ := leftDerivedUpperStarComp_hom_app_comp_counit A f g fg hfg
    (((h)^*[A].mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  have hc₂ := leftDerivedUpperStarComp_hom_app_comp_counit A fg h fgh hfgh K
  have hc₃ := leftDerivedUpperStarComp_hom_app_comp_counit A f gh fgh
    (by rw [hfgh, hfg, hgh, Category.assoc]) K
  have hc₄ := leftDerivedUpperStarComp_hom_app_comp_counit A g h gh hgh K
  have hnat := (leftDerivedUpperStarComp A f g fg hfg).hom.naturality
    ((h)^*[A].leftDerivedFunctorCounit.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hnat
  simp only [κ, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  rw [← reassoc_of% hnat, hc₁, reassoc_of% hc₂, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc, hc₄, Functor.map_comp, Functor.map_comp_assoc]
  have hnat' := (f)^*[A].leftDerivedFunctorCounit.naturality
    ((NatTrans.mapHomotopyCategory (upperStarComp A g h gh hgh).hom (ComplexShape.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl ((h)^*[A] ⋙ (g)^*[A]))
        (ComplexShape.up ℤ)).inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hnat'
  rw [hnat', reassoc_of% hc₃]
  simp only [← Functor.map_comp, Category.assoc]
  congr 2
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have key := NatTrans.congr_app (Etale.upperStarComp_assoc' A f g h fg gh fgh hfg hgh hfgh).symm
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at key
  simp only [mapHomotopyCategoryCompIso_inv_app_quotient, mapHomotopyCategory_app_quotient]
  erw [mapHomotopyCategoryCompIso_inv_app_quotient, mapHomotopyCategory_app_quotient]
  simp only [← Functor.map_comp]
  congr 1
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  simp only [HomotopyCategory.quotient_obj_as, HomologicalComplex.comp_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Functor.mapHomologicalComplex_map_f, Iso.refl_inv, Functor.map_comp]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  rw [NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact key (K.X n)

end Etale

end AlgebraicGeometry
