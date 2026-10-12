/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperStarMonoidal

/-!
# The tensor comparison of the pro-étale derived pullback commutes with shifts

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift`.

For `g : Z ⟶ Y`, we equip the derived pushforward `Rg_*` and the derived pullback `Lg^*` with
commutations with the shifts for which

* the adjunction `Lg^* ⊣ Rg_*` commutes with the shifts
  (`AlgebraicGeometry.ProEtale.commShift_derivedUpperStarLowerStarAdjunction'`), and both functors
  are triangulated;
* for a fixed `K`, the tensor comparison `Lg^*(K ⊗ᴸ -) ⟶ Lg^*K ⊗ᴸ Lg^*(-)`
  (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison`) commutes with the shifts
  (`AlgebraicGeometry.ProEtale.commShift_leftDerivedUpperStarTensorComparisonApp`).

## Implementation notes

The shift structures are the ones of the étale model: `Rg_*` is the right adjoint of the functor
`D(g^*)` induced by the exact pullback, and inherits its commutation with the shifts
(`AlgebraicGeometry.ProEtale.commShiftRightDerivedLowerStar'`), while `Lg^*` is isomorphic to
`D(g^*)` and receives its commutation with the shifts from this isomorphism
(`AlgebraicGeometry.ProEtale.commShiftLeftDerivedUpperStar'`). They are *not* instances: the
global instances of `WeilConjectures.SixFunctors.ProEtale.Derived.Shift` use instead the
commutation of the right derived functor `Rg_*` with the shifts computed with K-injective
resolutions, and the commutation of `Lg^*` with the shifts transported along the adjunction.
These definitions are meant to be activated locally, in proofs of statements (such as the
triangulatedness of a subcategory) which do not depend on the chosen shift structures.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section LowerStar

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The derived adjunction `D(g^*) ⊣ Rg_*` on the unbounded derived categories of pro-étale
sheaves, where the exact pullback `g^*` is applied levelwise. -/
noncomputable def mapDerivedUpperStarLowerStarAdjunction : D((g)^*[A]) ⊣ R((g)_*[A]) :=
  (ProEtale.upperStarLowerStarAdjunction A g).mapDerivedCategoryRightDerivedAdjunction

/-- The commutation of `Rg_*` with the shifts inherited from its left adjoint `D(g^*)`. It is not
an instance, see the implementation notes. -/
@[implicit_reducible]
noncomputable def commShiftRightDerivedLowerStar' : (R((g)_*[A])).CommShift ℤ :=
  (mapDerivedUpperStarLowerStarAdjunction A g).rightAdjointCommShift ℤ

attribute [local instance high] commShiftRightDerivedLowerStar'

/-- The adjunction `D(g^*) ⊣ Rg_*` commutes with the shifts, for
`AlgebraicGeometry.ProEtale.commShiftRightDerivedLowerStar'`. -/
lemma commShift_mapDerivedUpperStarLowerStarAdjunction :
    (mapDerivedUpperStarLowerStarAdjunction A g).CommShift ℤ :=
  (mapDerivedUpperStarLowerStarAdjunction A g).commShift_of_leftAdjoint ℤ

/-- `Rg_*` is triangulated, for `AlgebraicGeometry.ProEtale.commShiftRightDerivedLowerStar'`. -/
lemma isTriangulated_rightDerivedLowerStar' : (R((g)_*[A])).IsTriangulated :=
  have := commShift_mapDerivedUpperStarLowerStarAdjunction A g
  (mapDerivedUpperStarLowerStarAdjunction A g).isTriangulated_rightAdjoint

end LowerStar

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The commutation of `Lg^*` with the shifts transported from `D(g^*)` along
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarIsoMapDerivedCategory`. It is not an instance,
see the implementation notes. -/
@[implicit_reducible]
noncomputable def commShiftLeftDerivedUpperStar' : (L((g)^*[A])).CommShift ℤ :=
  Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ

attribute [local instance high] commShiftRightDerivedLowerStar' commShiftLeftDerivedUpperStar'

/-- `Lg^*` is triangulated, for `AlgebraicGeometry.ProEtale.commShiftLeftDerivedUpperStar'`. -/
lemma isTriangulated_leftDerivedUpperStar' : (L((g)^*[A])).IsTriangulated :=
  have := Functor.CommShift.ofIso_compatibility
    (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  Functor.isTriangulated_of_iso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm

/-- The derived adjunction `Lg^* ⊣ Rg_*` is the adjunction `D(g^*) ⊣ Rg_*` transported along
`Lg^* ≅ D(g^*)`. -/
lemma derivedUpperStarLowerStarAdjunction_eq :
    derivedUpperStarLowerStarAdjunction A g =
      (mapDerivedUpperStarLowerStarAdjunction A g).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory A g).symm :=
  Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
    (leftDerivedUpperStarIsoMapDerivedCategory A g)
    ((g)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac).symm

/-- The derived adjunction `Lg^* ⊣ Rg_*` commutes with the shifts, for
`AlgebraicGeometry.ProEtale.commShiftLeftDerivedUpperStar'` and
`AlgebraicGeometry.ProEtale.commShiftRightDerivedLowerStar'`. -/
lemma commShift_derivedUpperStarLowerStarAdjunction' :
    (derivedUpperStarLowerStarAdjunction A g).CommShift ℤ := by
  rw [derivedUpperStarLowerStarAdjunction_eq]
  have := commShift_mapDerivedUpperStarLowerStarAdjunction A g
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  exact Adjunction.commShift_ofNatIsoLeft _ _

/-- Tensoring on the left with a fixed complex, `M ↦ K ⊗ᴸ M`, commutes with shifts. -/
noncomputable instance commShiftDerivedTensorObj {X : Scheme.{u}}
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((derivedTensor A X).obj K).CommShift ℤ :=
  inferInstanceAs
    (((curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))).obj K).CommShift ℤ)

open DerivedCategory

/-- The counit `Qh ⋙ Lg^* ⟶ g^* ⋙ Qh` of the derived pullback commutes with the shifts. -/
instance commShift_leftDerivedFunctorCounit_upperStar :
    NatTrans.CommShift (g)^*[A].leftDerivedFunctorCounit ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ℤ :=
    inferInstanceAs
      (NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.inv ℤ)
  rw [← (g)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  exact inferInstanceAs (NatTrans.CommShift (Functor.whiskerLeft Qh
    (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ≫ _) ℤ)

section

variable [ProEtale.UpperStarPreservesFlat A]


/-- The tensor comparison `Lg^*(K ⊗ᴸ -) ⟶ Lg^*K ⊗ᴸ Lg^*(-)` for a fixed `K`. -/
noncomputable abbrev leftDerivedUpperStarTensorComparisonApp
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (-⊗ᴸ-(Y)[A]).obj K ⋙ L((g)^*[A]) ⟶ L((g)^*[A]) ⋙ (-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj K) :=
  (leftDerivedUpperStarTensorComparison A g).app K

lemma commShift_leftDerivedUpperStarTensorComparisonApp_of_iso
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)} (e : K ≅ K')
    [NatTrans.CommShift (leftDerivedUpperStarTensorComparisonApp A g K') ℤ] :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonApp A g K) ℤ := by
  have eq : leftDerivedUpperStarTensorComparisonApp A g K =
      Functor.whiskerRight ((-⊗ᴸ-(Y)[A]).map e.hom) L((g)^*[A]) ≫
        leftDerivedUpperStarTensorComparisonApp A g K' ≫
        Functor.whiskerLeft L((g)^*[A]) ((-⊗ᴸ-(Z)[A]).map (L((g)^*[A]).map e.inv)) := by
    have := (leftDerivedUpperStarTensorComparison A g).naturality e.hom
    ext M
    have := congr_app this M
    dsimp at this ⊢
    rw [reassoc_of% this, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp,
      e.hom_inv_id]
    simp
  have : NatTrans.CommShift ((-⊗ᴸ-(Y)[A]).map e.hom) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).map e.hom) ℤ)
  have : NatTrans.CommShift ((-⊗ᴸ-(Z)[A]).map (L((g)^*[A]).map e.inv)) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor _).map (L((g)^*[A]).map e.inv)) ℤ)
  rw [eq]
  infer_instance

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

lemma leftDerivedUpperStarTensorComparison_eq :
    leftDerivedUpperStarTensorComparison A g =
      Functor.leftDerived₂NatTrans _ (derivedTensorLeftDerivedUpperStarCounit A g)
        (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
        (leftDerivedUpperStarDerivedTensorCounit A g)
        (Functor.postcompose₂MapWhiskeringLeft₂
          (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh) :=
  rfl

/-- The defining property of the tensor comparison of `Lg^*`, on objects of the homotopy
category. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_app_app_fac
    (X M : HomotopyCategory (Sheaf (Scheme.ProEt.topology Y) A) (.up ℤ)) :
    ((leftDerivedUpperStarTensorComparison A g).app (Qh.obj X)).app (Qh.obj M) ≫
        ((derivedTensorLeftDerivedUpperStarCounit A g).app X).app M =
      ((leftDerivedUpperStarDerivedTensorCounit A g).app X).app M ≫
        ((Functor.postcompose₂MapWhiskeringLeft₂
          (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh).app X).app
            M := by
  rw [leftDerivedUpperStarTensorComparison_eq]
  exact Functor.leftDerived₂NatTrans_app_app _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (Functor.postcompose₂MapWhiskeringLeft₂
      (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh) X M

lemma commShift_leftDerivedUpperStarTensorComparisonApp_Qh_obj
    (X : HomotopyCategory (Sheaf (Scheme.ProEt.topology Y) A) (.up ℤ))
    (hX : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat X) (hgX : kFlatUpperStar A g X) :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonApp A g (Qh.obj X)) ℤ :=
  DerivedCategory.commShift_of_tensorLeft_fac (g)^*[A] L((g)^*[A])
    (g)^*[A].leftDerivedFunctorCounit X hX hgX _ (fun M ↦ by
      have := leftDerivedUpperStarTensorComparison_app_app_fac A g X M
      simp only [Functor.postcompose₂_obj_obj_obj_obj, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
        curriedTensor_obj_obj, derivedTensorLeftDerivedUpperStarCounit, NatTrans.comp_app,
        Functor.comp_obj, Functor.whiskeringLeft₂_map_app_app_app_app,
        Functor.whiskeringLeft₂_obj_map_app_app_app, Functor.whiskeringLeft₂_obj_obj_map_app_app,
        Functor.LaxMonoidal.μNatTrans_app_app, leftDerivedUpperStarDerivedTensorCounit,
        Functor.postcompose₂_obj_map_app_app, Functor.postcompose₂_map_app_app_app,
        Functor.postcompose₂MapWhiskeringLeft₂_app_app, Category.assoc] at this ⊢
      exact this)

/-- For a fixed `K`, the tensor comparison `Lg^*(K ⊗ᴸ -) ⟶ Lg^*K ⊗ᴸ Lg^*(-)` commutes with
the shifts. -/
instance commShift_leftDerivedUpperStarTensorComparisonApp
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    NatTrans.CommShift (leftDerivedUpperStarTensorComparisonApp A g K) ℤ := by
  let Λ :=
    (inferInstance : HasFunctorialFlatResolution (Sheaf (Scheme.ProEt.topology Y) A)).some.reduced
  let K₀ := DerivedCategory.Q.objPreimage K
  let R := Λ.resolutionFunctor.obj K₀
  have hR := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K₀
  have hgR := kFlatUpperStar_quotient_obj_resolutionFunctor_obj A g Λ K₀
  have := commShift_leftDerivedUpperStarTensorComparisonApp_Qh_obj A g
    ((HomotopyCategory.quotient _ _).obj R) ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hR) hgR
  let e : K ≅ Qh.obj ((HomotopyCategory.quotient _ _).obj R) :=
    (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app K₀))).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app R
  exact commShift_leftDerivedUpperStarTensorComparisonApp_of_iso A g e

end

end ProEtale

end AlgebraicGeometry
