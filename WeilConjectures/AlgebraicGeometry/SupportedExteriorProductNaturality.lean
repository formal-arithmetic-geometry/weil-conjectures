/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedExteriorProductNormalization
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit

/-!
# Naturality of the pairing of supported sections

The pullback and tensor of supported sections, its totalization, the comparison with the
derived exterior product and the support units are natural in the cochain complexes.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

section GlobalSections

variable (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]

/-- The support resolution unit is natural in the cochain complex. -/
@[reassoc]
theorem exteriorSupportResolutionUnit_naturality
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {P P' : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ} (φ : P ⟶ P') :
    DerivedCategory.Q.map (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).map φ) ≫
        exteriorSupportResolutionUnit C i P' =
      exteriorSupportResolutionUnit C i P ≫
        (rightDerivedSectionsWithSupport C i).map (DerivedCategory.Q.map φ) :=
  (globalSectionsWithSupport C i).rightDerivedFunctorUnitQ_naturality φ

end GlobalSections

section Naturality

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [HasSmallSiteSheafify C]

omit [HasSmallSiteSheafify C] in
/-- The tensor product of two localized chain maps followed by the tensor localization map. -/
@[reassoc]
theorem derivedTensorHom_Q_map_comp_μ {T : Scheme.{u}}
    {P P' Q Q' : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ} (φ : P ⟶ P') (ψ : Q ⟶ Q') :
    derivedTensorHom C (DerivedCategory.Q.map φ) (DerivedCategory.Q.map ψ) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q P' Q' =
      Functor.LaxMonoidal.μ DerivedCategory.Q P Q ≫ DerivedCategory.Q.map (tensorHom φ ψ) := by
  rw [derivedTensorHom]
  exact Functor.LaxMonoidal.μ_natural DerivedCategory.Q φ ψ

variable {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)

omit [HasSmallSiteSheafify C] in
/-- The comparison of the derived exterior product with the ordinary exterior complex is
natural in both cochain complexes. -/
@[reassoc]
theorem exteriorProductResolutionComparison_naturality
    {P P' : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ}
    {Q Q' : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ} (φ : P ⟶ P') (ψ : Q ⟶ Q') :
    derivedTensorHom C
        ((upperStar C (pullback.fst f g)).leftDerivedFunctor.map (DerivedCategory.Q.map φ))
        ((upperStar C (pullback.snd f g)).leftDerivedFunctor.map (DerivedCategory.Q.map ψ)) ≫
      exteriorProductResolutionComparison C f g P' Q' =
    exteriorProductResolutionComparison C f g P Q ≫
      DerivedCategory.Q.map (tensorHom
        (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).map φ)
        (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).map ψ)) := by
  let ε {T : Scheme.{u}} (h : pullback f g ⟶ T) :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
        (upperStar C h).leftDerivedFunctor ≫
      Functor.whiskerLeft (HomotopyCategory.quotient _ _)
        (upperStar C h).leftDerivedFunctorCounit ≫
      Functor.whiskerRight ((upperStar C h).mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft ((upperStar C h).mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso _).hom
  have h₁ := (ε (pullback.fst f g)).naturality φ
  have h₂ := (ε (pullback.snd f g)).naturality ψ
  dsimp only [ε, Functor.comp_map, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at h₁ h₂
  rw [exteriorProductResolutionComparison, exteriorProductResolutionComparison,
    derivedTensorHom_comp_assoc]
  erw [h₁, h₂]
  rw [← derivedTensorHom_comp_assoc]
  erw [derivedTensorHom_Q_map_comp_μ C
    (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).map φ)
    (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).map ψ)]
  rw [Category.assoc]

variable {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]

omit [Abelian.HasFunctorialFlatResolution C] [HasSmallSiteSheafify C] in
/-- The defining property of the totalized supported pairing. -/
@[reassoc]
theorem ιTensorObj_exteriorSupportedSectionsComplex_f
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) (r s n : ℤ) (h : r + s = n) :
    HomologicalComplex.ιTensorObj
        (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P)
        (((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).obj Q) r s n h ≫
      (exteriorSupportedSectionsComplex C f g i j P Q).f n =
    exteriorSupportedSections C f g i j (P.X r) (Q.X s) ≫
      (globalSectionsWithSupport C (supportedProductImmersion f g i j)).map
        (HomologicalComplex.ιTensorObj
          (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).obj P)
          (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).obj Q)
          r s n h) :=
  (existsUnique_exteriorSupportedSectionsComplex C f g i j P Q).exists.choose_spec r s n h

omit [Abelian.HasFunctorialFlatResolution C] [HasSmallSiteSheafify C] in
/-- The totalized supported pairing is natural in both cochain complexes. -/
@[reassoc]
theorem exteriorSupportedSectionsComplex_naturality
    {P P' : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ}
    {Q Q' : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ} (φ : P ⟶ P') (ψ : Q ⟶ Q') :
    tensorHom (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).map φ)
        (((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).map ψ) ≫
        exteriorSupportedSectionsComplex C f g i j P' Q' =
      exteriorSupportedSectionsComplex C f g i j P Q ≫
        ((globalSectionsWithSupport C (supportedProductImmersion f g i j)).mapHomologicalComplex
          (.up ℤ)).map
          (tensorHom (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).map φ)
            (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).map ψ)) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro r s h
  simp only [HomologicalComplex.comp_f]
  erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  rw [curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_def_assoc]
  erw [ιTensorObj_exteriorSupportedSectionsComplex_f C f g i j P' Q' r s n h,
    ιTensorObj_exteriorSupportedSectionsComplex_f_assoc C f g i j P Q r s n h]
  simp only [Functor.mapHomologicalComplex_map_f]
  rw [exteriorSupportedSections_naturality_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  erw [HomologicalComplex.ι_mapBifunctorMap]
  rw [curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_def_assoc]
  rfl

end Naturality

end AlgebraicGeometry.Etale
