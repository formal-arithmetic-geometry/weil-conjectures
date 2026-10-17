/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-!
# Proper coincidence: `Rf_! ≅ Rf_*` canonically

For a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, the *forget-supports* map
`ψ_c : Rf_!(c) = Rg_* D(i_!) ⟶ Rg_* Ri_* ⟶ Rf_*`. For a refinement of compactifications the
comparison of lower shrieks intertwines the forget-supports maps.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

/-- Associativity of the composition maps of derived pushforwards along a refinement. -/
lemma rightDerivedLowerStarCompHom_refinement_assoc
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedLowerStarCompHom A r.hom d.g c.g r.hom_g.symm).app (R((c.i)_*[A]).obj M) ≫
        (rightDerivedLowerStarCompHom A c.i c.g f c.comm).app M =
      R((d.g)_*[A]).map ((rightDerivedLowerStarCompHom A c.i r.hom d.i r.i_hom.symm).app M) ≫
        (rightDerivedLowerStarCompHom A d.i d.g f d.comm).app M := by
  have h := leftDerivedUpperStarComp_assoc' A c.i r.hom d.g d.i c.g f r.i_hom.symm
    r.hom_g.symm d.comm
  have e₁ := conjugateEquiv_whiskerRight
    ((derivedUpperStarLowerStarAdjunction A d.g).comp (derivedUpperStarLowerStarAdjunction A r.hom))
    (derivedUpperStarLowerStarAdjunction A c.g)
    (derivedUpperStarLowerStarAdjunction A c.i) (leftDerivedUpperStarComp A r.hom d.g c.g
      r.hom_g.symm).hom
  have e₂ := conjugateEquiv_whiskerLeft
    ((derivedUpperStarLowerStarAdjunction A r.hom).comp (derivedUpperStarLowerStarAdjunction A c.i))
    (derivedUpperStarLowerStarAdjunction A d.i)
    (derivedUpperStarLowerStarAdjunction A d.g) (leftDerivedUpperStarComp A c.i r.hom d.i
      r.i_hom.symm).hom
  have key : (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft R((c.i)_*[A])
        (rightDerivedLowerStarCompHom A r.hom d.g c.g r.hom_g.symm) ≫
        rightDerivedLowerStarCompHom A c.i c.g f c.comm =
      Functor.whiskerRight (rightDerivedLowerStarCompHom A c.i r.hom d.i r.i_hom.symm)
        R((d.g)_*[A]) ≫ rightDerivedLowerStarCompHom A d.i d.g f d.comm := by
    simp only [rightDerivedLowerStarCompHom]
    rw [← e₁, ← e₂, conjugateEquiv_comp, conjugateEquiv_comp, ← conjugateEquiv_associator_hom,
      conjugateEquiv_comp]
    congr 1
    rw [h]
    ext K
    simp
  have := NatTrans.congr_app key M
  simpa using this

variable [HasSmallSiteSheafify A]

/-- On sheaves: the base change `(c.i)_! ⟶ (d.i)_! ⋙ q^*` of a refinement is compatible with the
units of `(c.i)_! ⊣ (c.i)^*` and `(d.i)_! ⊣ (d.i)^*` through `(d.i)^* ≅ q^* ⋙ (c.i)^*`. -/
lemma unit_comp_map_refinementOpenImmersionLowerShriekBaseChange
    (M : Sheaf X.smallEtaleTopology A) :
    (openImmersionLowerShriekUpperStarAdjunction A c.i).unit.app M ≫
        ((c.i)^*[A]).map ((r.openImmersionLowerShriekBaseChange A).app M) =
      (openImmersionLowerShriekUpperStarAdjunction A d.i).unit.app M ≫
        (upperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app (((d.i)_!open[A]).obj M) := by
  have h := unit_conjugateEquiv ((openImmersionLowerShriekUpperStarAdjunction A d.i).comp
    (upperStarLowerStarAdjunction A r.hom)) (openImmersionLowerShriekUpperStarAdjunction A c.i)
    (r.openImmersionLowerShriekBaseChange A) M
  have hc : conjugateEquiv ((openImmersionLowerShriekUpperStarAdjunction A d.i).comp
      (upperStarLowerStarAdjunction A r.hom)) (openImmersionLowerShriekUpperStarAdjunction A c.i)
      (r.openImmersionLowerShriekBaseChange A) = upperStarBaseChange A c.i r.hom d.i r.i_hom := by
    simp [Compactification.Refinement.openImmersionLowerShriekBaseChange,
      Etale.openImmersionLowerShriekBaseChange]
  rw [hc, Adjunction.comp_unit_app, upperStarBaseChange_app, Category.assoc] at h
  rw [← h]
  congr 1
  have hn := (upperStarComp A c.i r.hom d.i r.i_hom.symm).hom.naturality
    ((upperStarLowerStarAdjunction A r.hom).unit.app (((d.i)_!open[A]).obj M))
  simp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  rw [← Functor.map_comp]
  simp

/-- The derived form of `unit_comp_map_refinementOpenImmersionLowerShriekBaseChange`, for a
refinement whose square over `X` is cartesian. -/
lemma derivedUnit_comp_map_refinementLowerShriekBaseChangeDerivedIso
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A c.i).unit.app M ≫
        D((c.i)^*[A]).map ((refinementLowerShriekBaseChangeDerivedIso A r hcart).hom.app M) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A d.i).unit.app M ≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp A c.i r.hom d.i r.i_hom.symm) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).hom.app (D((d.i)_!open[A]).obj M) := by
  haveI := r.isIso_openImmersionLowerShriekBaseChange A hcart
  exact Adjunction.mapDerivedCategoryAdjunction_mate'
    (openImmersionLowerShriekUpperStarAdjunction A d.i)
    (openImmersionLowerShriekUpperStarAdjunction A c.i)
    (upperStarComp A c.i r.hom d.i r.i_hom.symm) (asIso (r.openImmersionLowerShriekBaseChange A))
    (fun K ↦ unit_comp_map_refinementOpenImmersionLowerShriekBaseChange A r K) M

/-- The transpose of the comparison `D(j_!) ⟶ Rj_*` under `D(j^*) ⊣ Rj_*` is the inverse of the
unit of `D(j_!) ⊣ D(j^*)`. -/
@[reassoc]
lemma map_derivedOpenImmersionLowerShriekToLowerStar_app_comp_counit {U Z : Scheme.{u}}
    (j : U ⟶ Z) [IsOpenImmersion j] (M : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    D((j)^*[A]).map ((derivedOpenImmersionLowerShriekToLowerStar A j).app M) ≫
        (mapDerivedUpperStarLowerStarAdjunction A j).counit.app M =
      inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app M) := by
  have hn := (mapDerivedUpperStarLowerStarAdjunction A j).counit.naturality
    (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app M))
  simp only [Functor.comp_map, Functor.id_map] at hn
  simp only [derivedOpenImmersionLowerShriekToLowerStar, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    NatIso.isIso_inv_app, Category.id_comp, Functor.map_comp, Category.assoc, hn]
  rw [← Category.assoc, Adjunction.left_triangle_components, Category.id_comp]

end Etale

end AlgebraicGeometry
