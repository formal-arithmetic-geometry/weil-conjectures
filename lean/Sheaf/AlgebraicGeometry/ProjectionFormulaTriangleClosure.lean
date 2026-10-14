/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Triangulated.Adjunction
/-! The canonical projection map is invertible on the third vertex of a distinguished
triangle whenever it is invertible on the first two vertices. -/

@[expose] public section
universe u' u
open CategoryTheory Abelian Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open Scheme
variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
@[instance_reducible]
private noncomputable def shiftPush {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (R((g)_*[A])).CommShift ℤ :=
  (mapDerivedUpperStarLowerStarAdjunction A g).rightAdjointCommShift ℤ
@[instance_reducible]
private noncomputable def shiftPull {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (L((g)^*[A])).CommShift ℤ :=
  Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
attribute [local instance] shiftPush shiftPull
@[instance_reducible]
private noncomputable def shiftTensor {X : Scheme.{u}}
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((-⊗ᴸ-(X)[A]).obj K).CommShift ℤ :=
  inferInstanceAs (((curriedTensor
    (DerivedCategory (Sheaf X.smallEtaleTopology A))).obj K).CommShift ℤ)
attribute [local instance] shiftTensor
omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A] in
private lemma shiftMapAdj {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (mapDerivedUpperStarLowerStarAdjunction A g).CommShift ℤ :=
  (mapDerivedUpperStarLowerStarAdjunction A g).commShift_of_leftAdjoint ℤ
attribute [local instance] shiftMapAdj
variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
open DerivedCategory

/-- The counit `Qh ⋙ Lg^* ⟶ g^* ⋙ Qh` of the derived pullback commutes with the shifts. -/
private lemma shiftCounit :
    NatTrans.CommShift (g)^*[A].leftDerivedFunctorCounit ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ℤ :=
    inferInstanceAs
      (NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.inv ℤ)
  rw [← (g)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  exact inferInstanceAs (NatTrans.CommShift (Functor.whiskerLeft Qh
    (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ≫ _) ℤ)

attribute [local instance] shiftCounit

section

variable [(g)^*[A].PreservesFlat]


/-- The tensor comparison `Lg^*(K ⊗ᴸ -) ⟶ Lg^*K ⊗ᴸ Lg^*(-)` for a fixed `K`. -/
private noncomputable abbrev comparisonApp
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (curriedTensor (DerivedCategory (Sheaf Y.smallEtaleTopology A))).obj K ⋙ L((g)^*[A]) ⟶
      L((g)^*[A]) ⋙ (curriedTensor (DerivedCategory (Sheaf Z.smallEtaleTopology A))).obj
        (L((g)^*[A]).obj K) :=
  (leftDerivedUpperStarTensorComparison A g).app K

private lemma shiftComparison_of_iso
    {K K' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (e : K ≅ K')
    [NatTrans.CommShift (comparisonApp A g K') ℤ] :
    NatTrans.CommShift (comparisonApp A g K) ℤ := by
  have eq : comparisonApp A g K =
      Functor.whiskerRight ((-⊗ᴸ-(Y)[A]).map e.hom) L((g)^*[A]) ≫
        comparisonApp A g K' ≫
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

private lemma comparison_eq :
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
private lemma comparison_fac
    (X M : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ)) :
    ((leftDerivedUpperStarTensorComparison A g).app (Qh.obj X)).app (Qh.obj M) ≫
        ((derivedTensorLeftDerivedUpperStarCounit A g).app X).app M =
      ((leftDerivedUpperStarDerivedTensorCounit A g).app X).app M ≫
        ((Functor.postcompose₂MapWhiskeringLeft₂
          (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh).app X).app
            M := by
  rw [comparison_eq]
  exact Functor.leftDerived₂NatTrans_app_app _ (derivedTensorLeftDerivedUpperStarCounit A g)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (leftDerivedUpperStarDerivedTensorCounit A g)
    (Functor.postcompose₂MapWhiskeringLeft₂
      (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) (g)^*[A]) Qh) X M

private lemma shiftComparison_Qh
    (X : HomotopyCategory (Sheaf Y.smallEtaleTopology A) (.up ℤ))
    (hX : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat X) (hgX : kFlatUpperStar A g X) :
    NatTrans.CommShift (comparisonApp A g (Qh.obj X)) ℤ :=
  DerivedCategory.commShift_of_tensorLeft_fac (g)^*[A] L((g)^*[A])
    (g)^*[A].leftDerivedFunctorCounit X hX hgX _ (fun M ↦ by
      have := comparison_fac A g X M
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
private lemma shiftComparison
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    NatTrans.CommShift (comparisonApp A g K) ℤ := by
  let Λ := (inferInstance : HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A)).some.reduced
  let K₀ := DerivedCategory.Q.objPreimage K
  let R := Λ.resolutionFunctor.obj K₀
  have hR := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K₀
  have hgR := kFlatUpperStar_quotient_obj_resolutionFunctor_obj A g Λ K₀
  have := shiftComparison_Qh A g
    ((HomotopyCategory.quotient _ _).obj R) ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hR) hgR
  let e : K ≅ Qh.obj ((HomotopyCategory.quotient _ _).obj R) :=
    (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
      (asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app K₀))).symm ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app R
  exact shiftComparison_of_iso A g e


attribute [local instance] shiftComparison
end
private lemma shiftAdjunction {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (derivedUpperStarLowerStarAdjunction A g).CommShift ℤ := by
  have he : derivedUpperStarLowerStarAdjunction A g =
      (mapDerivedUpperStarLowerStarAdjunction A g).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory A g).symm :=
    Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
      (leftDerivedUpperStarIsoMapDerivedCategory A g)
      ((g)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac).symm
  rw [he]
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  exact Adjunction.commShift_ofNatIsoLeft _ _
attribute [local instance] shiftAdjunction
private lemma shiftProjection [UpperStarPreservesFlat A] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    NatTrans.CommShift (F₁ := (curriedTensor
      (DerivedCategory (Sheaf Y.smallEtaleTopology A))).obj (R((p)_*[A]).obj M))
      (F₂ := (L((p)^*[A]) ⋙ (curriedTensor
        (DerivedCategory (Sheaf X.smallEtaleTopology A))).obj M) ⋙ R((p)_*[A]))
      ((rightDerivedLowerStarProjectionMap A p).app M) ℤ := by
  have : NatTrans.CommShift (F₁ := (curriedTensor
      (DerivedCategory (Sheaf Y.smallEtaleTopology A))).obj
        (R((p)_*[A]).obj M) ⋙ L((p)^*[A]))
      (F₂ := L((p)^*[A]) ⋙ (curriedTensor (DerivedCategory (Sheaf X.smallEtaleTopology A))).obj
        (L((p)^*[A]).obj (R((p)_*[A]).obj M)))
      ((leftDerivedUpperStarTensorComparison A p).app (R((p)_*[A]).obj M)) ℤ :=
    shiftComparison A p (R((p)_*[A]).obj M)
  have : NatTrans.CommShift (F₁ := (-⊗ᴸ-(X)[A]).obj
      (L((p)^*[A]).obj (R((p)_*[A]).obj M)))
      (F₂ := (-⊗ᴸ-(X)[A]).obj M)
      ((-⊗ᴸ-(X)[A]).map ((derivedUpperStarLowerStarAdjunction A p).counit.app M)) ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor
      (DerivedCategory (Sheaf X.smallEtaleTopology A))).map
        ((derivedUpperStarLowerStarAdjunction A p).counit.app M)) ℤ)
  exact Adjunction.commShift_rightAdjointProjectionMap_app
    (derivedUpperStarLowerStarAdjunction A p) (leftDerivedUpperStarTensorComparison A p) M

/-- The isomorphism locus of the projection map is closed under distinguished triangles.
Source: Stacks Project, Tag 0F12, property (2), and Tag 014A.
(blueprint: lem-etale-projection-formula-triangle-closure)
Proof in words: pullback, pushforward and tensor are triangulated functors. The tensor
comparison and derived adjunction commute with shift, so the canonical projection map
induces a morphism between the images of a distinguished triangle. The first two
components are isomorphisms by hypothesis. The triangulated five lemma gives the third. -/
theorem projection_triangle_isIso [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (T : Pretriangulated.Triangle (DerivedCategory (Sheaf Y.smallEtaleTopology A)))
    (ht : T ∈ Pretriangulated.distinguishedTriangles)
    (h₁ : IsIso (((rightDerivedLowerStarProjectionMap A p).app M).app T.obj₁))
    (h₂ : IsIso (((rightDerivedLowerStarProjectionMap A p).app M).app T.obj₂)) :
    IsIso (((rightDerivedLowerStarProjectionMap A p).app M).app T.obj₃) := by
  let F := (-⊗ᴸ-(Y)[A]).obj (R((p)_*[A]).obj M)
  let G := (L((p)^*[A]) ⋙ (-⊗ᴸ-(X)[A]).obj M) ⋙ R((p)_*[A])
  let α : F ⟶ G := (rightDerivedLowerStarProjectionMap A p).app M
  have : F.IsTriangulated := inferInstanceAs
    (Functor.IsTriangulated (tensorLeft (R((p)_*[A]).obj M)))
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A p).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A p).symm ℤ
  have : (L((p)^*[A])).IsTriangulated :=
    Functor.isTriangulated_of_iso (leftDerivedUpperStarIsoMapDerivedCategory A p).symm
  have : (R((p)_*[A])).IsTriangulated :=
    (mapDerivedUpperStarLowerStarAdjunction A p).isTriangulated_rightAdjoint
  have : ((-⊗ᴸ-(X)[A]).obj M).IsTriangulated :=
    inferInstanceAs (Functor.IsTriangulated (tensorLeft M))
  have : NatTrans.CommShift α ℤ := shiftProjection A p M
  let φ : F.mapTriangle.obj T ⟶ G.mapTriangle.obj T :=
    { hom₁ := α.app T.obj₁
      hom₂ := α.app T.obj₂
      hom₃ := α.app T.obj₃
      comm₁ := α.naturality T.mor₁
      comm₂ := α.naturality T.mor₂
      comm₃ := by
        change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
          (α.app T.obj₁)⟦(1 : ℤ)⟧' =
          α.app T.obj₃ ≫ G.map T.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁
        rw [Category.assoc, NatTrans.shift_app_comm α (1 : ℤ) T.obj₁,
          ← Category.assoc, α.naturality T.mor₃, Category.assoc] }
  exact Pretriangulated.isIso₃_of_isIso₁₂ φ
    (F.map_distinguished T ht) (G.map_distinguished T ht) h₁ h₂

end AlgebraicGeometry.Etale
