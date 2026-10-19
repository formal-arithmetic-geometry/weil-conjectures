/-
Copyright (c) 2026 Joël Riou, Claude and the SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude, SHEAF group C3
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.DerivedCategory.ModuleCatGeneration
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import Sheaf.CategoryTheory.DerivedMonoidalComparisonShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapUnit

/-!
# Compact-support projection for finite constant coefficients

Source: the coefficient argument in ExceptionalAdjointAdmissibility,
Stacks Tags 06YY and 07A6.
(blueprint: lem-sf-finite-support-projection).

The proper projection map is computed at an extension by zero. The open projection
isomorphism and the compact-support adjunction make its target a left adjoint.
Generation of the derived category of modules by the ring proves invertibility.
-/

@[expose] public section
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

private theorem projection_target_leftAdjoint
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (Lg : C ⥤ D) (Lj : D ⥤ E) (T : E ⥤ E) (J : E ⥤ D) (G : D ⥤ H)
    (S : D ⥤ D) (e : S ≅ (Lj ⋙ T) ⋙ J)
    [Lg.IsLeftAdjoint]
    [Lj.IsLeftAdjoint]
    [T.IsLeftAdjoint]
    [(J ⋙ G).IsLeftAdjoint] :
    ((Lg ⋙ S) ⋙ G).IsLeftAdjoint := by
  let e' : (Lg ⋙ S) ⋙ G ≅ (Lg ⋙ (Lj ⋙ T)) ⋙ (J ⋙ G) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft Lg (Functor.isoWhiskerRight e G) ≪≫
      Functor.isoWhiskerLeft Lg (Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm
  exact Functor.isLeftAdjoint_of_iso e'.symm

private noncomputable instance commShiftLeftDerivedUpperStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (L((g)^*[A])).CommShift ℤ :=
  Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ

attribute [local instance] ProEtale.sheafMonoidalCategory in
private noncomputable instance commShiftDerivedTensorObj {X : Scheme.{u}}
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((derivedTensor A X).obj K).CommShift ℤ :=
  inferInstanceAs
    (((curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))).obj K).CommShift ℤ)

attribute [local instance] ProEtale.sheafMonoidalCategory in
private noncomputable instance commShiftDerivedTensorFlipObj {X : Scheme.{u}}
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((derivedTensor A X).flip.obj K).CommShift ℤ :=
  inferInstanceAs
    (((curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))).flip.obj K).CommShift ℤ)

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

open _root_.DerivedCategory

attribute [local instance] ProEtale.sheafMonoidalCategory in
private instance derivedTensor_triangulated {X : Scheme.{u}}
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    ((derivedTensor A X).obj K).IsTriangulated :=
  inferInstanceAs (((curriedTensor _).obj K).IsTriangulated)

private instance commShift_leftDerivedFunctorCounit_upperStar :
    NatTrans.CommShift (g)^*[A].leftDerivedFunctorCounit ℤ := by
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ℤ :=
    inferInstanceAs
      (NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.inv ℤ)
  rw [← (g)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  exact inferInstanceAs (NatTrans.CommShift (Functor.whiskerLeft Qh
    (leftDerivedUpperStarIsoMapDerivedCategory A g).hom ≫ _) ℤ)

variable [ProEtale.UpperStarPreservesFlat A]

attribute [local instance] ProEtale.sheafMonoidalCategory in
private theorem comparison_generic :
    leftDerivedUpperStarTensorComparison A g = (g)^*[A].leftDerivedTensorComparison := rfl

private instance comparison_commShift
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    NatTrans.CommShift
      (F₁ := (-⊗ᴸ-(Y)[A]).obj K ⋙ L((g)^*[A]))
      (F₂ := L((g)^*[A]) ⋙ (-⊗ᴸ-(Z)[A]).obj (L((g)^*[A]).obj K))
      ((leftDerivedUpperStarTensorComparison A g).app K) ℤ := by
  rw [comparison_generic]
  exact GenericDerivedTensorShift.commShift (g)^*[A] K

private noncomputable abbrev mapDerivedUpperStarLowerStarAdjunction :
    D((g)^*[A]) ⊣ R((g)_*[A]) :=
  (upperStarLowerStarAdjunction A g).mapDerivedCategoryRightDerivedAdjunction

private noncomputable instance commShiftRightDerivedLowerStar {Z Y : Scheme.{u}}
    (g : Z ⟶ Y) : (R((g)_*[A])).CommShift ℤ :=
  (mapDerivedUpperStarLowerStarAdjunction A g).rightAdjointCommShift ℤ

private instance commShift_mapDerivedUpperStarLowerStarAdjunction :
    (mapDerivedUpperStarLowerStarAdjunction A g).CommShift ℤ :=
  (mapDerivedUpperStarLowerStarAdjunction A g).commShift_of_leftAdjoint ℤ

omit [ProEtale.UpperStarPreservesFlat A] in
private theorem derivedUpperStarLowerStarAdjunction_eq {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    derivedUpperStarLowerStarAdjunction A g =
      (mapDerivedUpperStarLowerStarAdjunction A g).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory A g).symm :=
  Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
    (leftDerivedUpperStarIsoMapDerivedCategory A g)
    ((g)^*[A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac).symm

private instance commShift_derivedUpperStarLowerStarAdjunction {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (derivedUpperStarLowerStarAdjunction A g).CommShift ℤ := by
  rw [derivedUpperStarLowerStarAdjunction_eq]
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  exact Adjunction.commShift_ofNatIsoLeft _ _

private instance commShift_derivedTensor_map {X : Scheme.{u}}
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (φ : K ⟶ K') :
    NatTrans.CommShift ((-⊗ᴸ-(X)[A]).map φ) ℤ :=
  inferInstanceAs (NatTrans.CommShift
    ((curriedTensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))).map φ) ℤ)

private instance commShift_rightDerivedLowerStarProjectionMap_app {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    NatTrans.CommShift (F₁ := (-⊗ᴸ-(Y)[A]).obj (R((p)_*[A]).obj M))
      (F₂ := (L((p)^*[A]) ⋙ (-⊗ᴸ-(X)[A]).obj M) ⋙ R((p)_*[A]))
      ((rightDerivedLowerStarProjectionMap A p).app M) ℤ :=
  Adjunction.commShift_rightAdjointProjectionMap_app (derivedUpperStarLowerStarAdjunction A p)
    (leftDerivedUpperStarTensorComparison A p) M

private instance rightDerivedLowerStar_triangulated {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (R((g)_*[A])).IsTriangulated :=
  (mapDerivedUpperStarLowerStarAdjunction A g).isTriangulated_rightAdjoint

private instance leftDerivedUpperStar_triangulated {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (L((g)^*[A])).IsTriangulated := by
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  exact Functor.isTriangulated_of_iso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm

private theorem projection_unit
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) :
    IsIso (((rightDerivedLowerStarProjectionMap A g).app K).app (𝟙_ _)) := by
  let := GenericDerivedTensorShift.oplaxMonoidal (g)^*[A]
  have := GenericDerivedTensorShift.isIso_unit (g)^*[A]
  exact Adjunction.isIso_rightAdjointProjectionMap_app_app_tensorUnit
    (derivedUpperStarLowerStarAdjunction A g) (leftDerivedUpperStarTensorComparison A g)
    (fun _ _ ↦ by rw [comparison_generic]; rfl) K

private theorem support_target_leftAdjoint
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [(Rf_!(c)[A]).IsLeftAdjoint]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (((upperStar A c.g).leftDerivedFunctor ⋙
        (derivedTensor A c.Z).obj ((openImmersionLowerShriek A c.i).mapDerivedCategory.obj K)) ⋙
        (lowerStar A c.g).rightDerivedFunctor).IsLeftAdjoint := by
  let Lg := (upperStar A c.g).leftDerivedFunctor
  let Lj := (upperStar A c.i).leftDerivedFunctor
  let J := (openImmersionLowerShriek A c.i).mapDerivedCategory
  let G := (lowerStar A c.g).rightDerivedFunctor
  let T := (derivedTensor A X).obj K
  have hLg : Lg.IsLeftAdjoint := (derivedUpperStarLowerStarAdjunction A c.g).isLeftAdjoint
  have hLj : Lj.IsLeftAdjoint := (derivedUpperStarLowerStarAdjunction A c.i).isLeftAdjoint
  have hT : T.IsLeftAdjoint := (derivedTensorHomAdjunction A K).isLeftAdjoint
  have hJG : (J ⋙ G).IsLeftAdjoint := inferInstanceAs ((Rf_!(c)[A]).IsLeftAdjoint)
  exact
    projection_target_leftAdjoint Lg Lj T J G _
      ((derivedOpenImmersionLowerShriekProjectionIso A c.i).symm.app K)

/-- The canonical compact-support projection component. The named irreducible component
avoids expanding the composed functor data during scalar/realization transport.
(blueprint: lem-sf-finite-support-projection). -/
@[irreducible]
noncomputable def compactSupportProjectionComponent
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ((derivedTensorRightDerivedLowerShriek A c).obj K).obj L ⟶
      ((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar A c).obj K).obj L :=
  ((projectionMapOfCompactification A c).app K).app L

/-- Computation of the named projection component. -/
theorem compactSupportProjectionComponent_eq
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    compactSupportProjectionComponent A c K L =
      ((projectionMapOfCompactification A c).app K).app L := by
  unfold compactSupportProjectionComponent
  rfl

end ProEtale
end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

private theorem constant_projection_of_leftAdjoint_target
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U T : Scheme.{u}} (p : U ⟶ T)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} R)))
    [(((upperStar (ModuleCat.{u + 1} R) p).leftDerivedFunctor ⋙
        (derivedTensor (ModuleCat.{u + 1} R) U).obj K) ⋙
        (lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor).IsLeftAdjoint]
    (N : ModuleCat.{u + 1} R) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) p).app K).app
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)).obj N))) := by
  let c := (constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)).mapDerivedCategory
  let τ : (derivedTensor (ModuleCat.{u + 1} R) T).obj
      ((lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.obj K) ⟶
      ((upperStar (ModuleCat.{u + 1} R) p).leftDerivedFunctor ⋙
        (derivedTensor (ModuleCat.{u + 1} R) U).obj K) ⋙
        (lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor :=
    (rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) p).app K
  let α := Functor.whiskerLeft c τ
  have hunit : IsIso (α.app
      ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of R R))) := by
    have h : IsIso (τ.app (𝟙_ _)) := projection_unit _ p K
    change IsIso (τ.app (c.obj _))
    refine (NatTrans.isIso_app_iff_of_iso τ ?_).2 h
    exact (Functor.mapDerivedCategorySingleFunctor _ 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (Functor.Monoidal.εIso
        (constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R))).symm ≪≫
      DerivedCategory.singleFunctorObjUnitIso _
  have hshift : NatTrans.CommShift α ℤ := inferInstance
  have hc : c.IsLeftAdjoint := by
    have := (constantSheafΓAdj (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} R)).derivedAdjunction.isLeftAdjoint
    exact Functor.isLeftAdjoint_of_iso
      (Functor.leftDerivedFunctorIsoMapDerivedCategory
        (constantSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} R)))
  have hF : ((derivedTensor (ModuleCat.{u + 1} R) T).obj
      ((lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.obj K)).IsLeftAdjoint :=
    (derivedTensorHomAdjunction (ModuleCat.{u + 1} R) _).isLeftAdjoint
  have hcTri : c.IsTriangulated := inferInstance
  have : IsIso α := DerivedCategory.isIso_of_isIso_app_singleFunctor_obj_self α hunit
  have hN : IsIso (α.app ((DerivedCategory.singleFunctor _ 0).obj N)) := inferInstance
  exact (NatTrans.isIso_app_iff_of_iso τ
    ((Functor.mapDerivedCategorySingleFunctor _ 0).app N)).1 hN

/-- The compact-support projection formula for constant coefficient modules over a finite ring.

Source: the coefficient argument in `ExceptionalAdjointAdmissibility`, Stacks Tags
06YY and 07A6, and the existing module-derived-category generation theorem.
(blueprint: lem-sf-finite-support-projection).

Proof: precompose the proper projection map at the extension by zero of K with the
exact derived constant-sheaf functor. The unit component is an isomorphism by monoidal
unitality, and the comparison commutes with shifts. Its source is a left adjoint by
tensor-Hom adjunction. For its target, the open projection isomorphism moves extension
by zero outside tensor and identifies the target with a composite of inverse images,
tensor and compact support, all left adjoints. Thus both functors preserve all small
coproducts. Generation of D(R) by R[0] proves the precomposed comparison invertible.
Evaluate at N[0] and use the exact constant-sheaf/single comparison. The remaining
factors of the compact-support projection are canonical isomorphisms. -/
theorem finite_support_projection
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [(Rf_!(c)[ModuleCat.{u + 1} R]).IsLeftAdjoint]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))
    (N : ModuleCat.{u + 1} R) :
    IsIso (compactSupportProjectionComponent (ModuleCat.{u + 1} R) c K
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R)).obj N))) := by
  rw [compactSupportProjectionComponent_eq]
  have htarget := support_target_leftAdjoint (ModuleCat.{u + 1} R) c K
  have hproper := constant_projection_of_leftAdjoint_target R c.g
    ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.obj K) N
  rw [projectionMapOfCompactification_app_app]
  exact inferInstance

end AlgebraicGeometry.ProEtale
