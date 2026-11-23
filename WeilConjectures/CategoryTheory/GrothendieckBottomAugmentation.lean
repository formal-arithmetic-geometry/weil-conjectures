/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import WeilConjectures.CategoryTheory.CanonicalResolutionDerivedIso
import WeilConjectures.CategoryTheory.GrothendieckBottomEdgeSingleUnit
import WeilConjectures.CategoryTheory.ResolutionDerivedSingleUnitAugmentation

/-! # The bottom interval and an augmented comparison

Source: Stacks Project, Tags 015N and 015J, bottom interval of the second spectral sequence.
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Before identifying the abutment with the derived composite, the bottom edge is
homology of the augmented comparison after applying the second derived functor.
No composite acyclicity hypothesis or resolution computation for G is used here.

Source: Stacks Project, Tags 015N and 015J. -/
theorem grothendieckBottomEdge_augmentation
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F]
    (X : A) (I : InjectiveResolution X) (J : InjectiveResolution (F.obj X))
    (φ : J.cocomplex ⟶ (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 = F.map (I.ι.f 0)) (n : ℕ) :
    let K := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    let L : CochainComplex.Plus B :=
      ⟨K.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
    let f : (⟨J.cochainComplex, 0, inferInstance⟩ : CochainComplex.Plus B) ⟶ L :=
      ObjectProperty.homMk (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
    (F.grothendieckBottomEdgeSourceIso G n).inv.app X ≫
        (F.grothendieckBottomEdge G n).app X ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlus.map (canonicalResolutionDerivedIso F I).hom) =
      (G.homologyRightDerivedFunctorPlusObjSingleFunctorIso (F.obj X) n).inv ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlus.map (resolutionAugmentationIso J).hom) ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f)) := by
  rw [← Category.assoc, grothendieckBottomEdge_singleUnit F G X n]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [resolutionDerivedSingleUnit_augmentation F X I J φ hφ]

end CategoryTheory
