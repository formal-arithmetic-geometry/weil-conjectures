/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.SupportScalarProjectionIdentification
import Sheaf.Paper.FiniteSupportProjection
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Coefficient comparison from the finite constant projection formula

Source: the coefficient paragraph of ExceptionalAdjointAdmissibility.
(blueprint: lem-sf-support-coefficient-by-projection).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

private theorem isIso_of_reflected_arrow_iso
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) [F.ReflectsIsomorphisms] [G.ReflectsIsomorphisms]
    {X Y : C} (f : X ⟶ Y) {Z W : E} (g : Z ⟶ W) (hg : IsIso g)
    (e : Arrow.mk (G.map (F.map f)) ≅ Arrow.mk g) : IsIso f := by
  have := (Arrow.isIso_iff_isIso_of_isIso e.hom).2 hg
  have : IsIso (F.map f) := isIso_of_reflects_iso _ G
  exact isIso_of_reflects_iso _ F

private theorem isLeftAdjoint_of_adjoint_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (EX : C' ≌ C) (EY : D' ≌ D) (F : C ⥤ D) (G : D ⥤ C) (F' : C' ⥤ D')
    (a : F ⊣ G) (e : EX.functor ⋙ F ≅ F' ⋙ EY.functor) :
    F'.IsLeftAdjoint := by
  let d : (EX.functor ⋙ F) ⋙ EY.inverse ≅ F' :=
    Functor.isoWhiskerRight e EY.inverse ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F' EY.unitIso.symm ≪≫ Functor.rightUnitor F'
  have : ((EX.functor ⋙ F) ⋙ EY.inverse).IsLeftAdjoint :=
    ((EX.toAdjunction.comp a).comp EY.symm.toAdjunction).isLeftAdjoint
  exact Functor.isLeftAdjoint_of_iso d

private noncomputable def intrinsicOpenComparison
    (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (sfIntrinsicModuleEquivalence U A).functor ⋙ sfIntrinsicExtensionByZero j A ≅
      ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        (sfIntrinsicModuleEquivalence X A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence U A).unitIso.symm _ ≪≫
    Functor.leftUnitor _

private noncomputable def intrinsicSupportComparison
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfAmbientCompactSupportCandidate A c ≅
      ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c ⋙
        (sfIntrinsicDerivedEquivalence Y A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (intrinsicOpenComparison A c.i) ≪≫
        Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntrinsicDerivedDirectImageComparison c.g A) ≪≫
    (Functor.associator _ _ _).symm

private theorem coefficient_restrict_reflects
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    (proEtaleCoefficientRestrictScalars T φ).mapDerivedCategory.ReflectsIsomorphisms := by
  have : (proEtaleCoefficientRestrictScalars T φ).ReflectsIsomorphisms :=
    (proEtaleRingRestrictScalars_properties
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom φ.ulift))).2.2
  refine ⟨fun f _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso ((proEtaleCoefficientRestrictScalars T φ).map
      ((DerivedCategory.homologyFunctor _ n).map f)) :=
    (NatIso.isIso_map_iff
      ((proEtaleCoefficientRestrictScalars T φ).mapDerivedCategoryHomologyFunctorIso n) f).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ (proEtaleCoefficientRestrictScalars T φ)


/-- An ambient compact-support right adjoint supplies the left-adjoint hypothesis
of the constant coefficient projection formula. After the scalar/projection identification,
conservativity of realization and exact scalar restriction proves the coefficient mate
invertible. Source: Stacks Tags 06YY, 07A6 and 0GL6.
(blueprint: lem-sf-support-coefficient-by-projection). -/
theorem supportCoefficient_isIso_of_projection
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (LX : proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory X B)
    (LY : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory Y B)
    (aX : LX ⊣ (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory)
    (aY : LY ⊣ (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory)
    {G : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory X A}
    (a : sfAmbientCompactSupportCandidate A c ⊣ G)
    (K : proEtaleDerivedCategory X A) :
    IsIso ((((mateEquiv aX aY).symm
      (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom)).natTrans).app K) := by
  let EX := sfIntrinsicDerivedEquivalence X A
  let EY := sfIntrinsicDerivedEquivalence Y A
  let F := ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c
  have : F.IsLeftAdjoint :=
    isLeftAdjoint_of_adjoint_transport EX EY _ G F a (intrinsicSupportComparison A c)
  let : Algebra (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) := φ.ulift.toAlgebra
  have hp := ProEtale.finite_support_projection (ULift.{u + 1, u} A) c
    ((projectionRealizationInverse X A).obj K)
    (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} B))
  obtain ⟨e⟩ := support_scalar_projection_identification φ c LX LY aX aY K
  have := coefficient_restrict_reflects φ Y
  refine isIso_of_reflected_arrow_iso
    (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory
    (projectionRealizationInverse Y A) _ _ ?_ e
  exact hp

end WeilConjectures
