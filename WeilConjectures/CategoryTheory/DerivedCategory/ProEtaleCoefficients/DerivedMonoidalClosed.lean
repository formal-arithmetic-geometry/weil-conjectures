/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory

/-!
# Closedness of the derived tensor product
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory

namespace DerivedCategory

/-- Tensoring on the left by any object
of the unbounded derived category has a right adjoint. -/
theorem tensorLeft_isLeftAdjoint_of_hasFunctorialFlatResolution
    (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]
    (K : DerivedCategory C) : (tensorLeft K).IsLeftAdjoint := by
  have (X : C) : Limits.PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X) :=
    Limits.preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  -- Work with a homotopy-category representative of the given derived object.
  let P := (Qh (C := C)).objPreimage K
  let H := HomotopyCategory.internalHom P ⋙ (Qh (C := C))
  let R := H.totalRightDerived Qh (HomotopyCategory.quasiIso C (.up ℤ))
  let η : H ⟶ Qh ⋙ R :=
    H.totalRightDerivedUnit Qh (HomotopyCategory.quasiIso C (.up ℤ))
  have : R.IsRightDerivedFunctor η (HomotopyCategory.quasiIso C (.up ℤ)) := by
    dsimp only [R, η]
    infer_instance
  -- K-flat and K-injective computation give the two absoluteness hypotheses.
  have : (tensorLeft (Qh.obj P) ⋙ R).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (tensorLeftQhObjCounit P) R)
      (HomotopyCategory.quasiIso C (.up ℤ)) :=
    (HomotopyCategory.quasiIso C (.up ℤ)).localizerMorphismKFlat
      |>.isLeftDerivedFunctor_comp_of_isLeftDerivabilityStructure _
        (fun Z ↦ isIso_tensorLeftQhObjCounit_app P Z.1 Z.2) _
  have : (R ⋙ tensorLeft (Qh.obj P)).IsRightDerivedFunctor
      (Functor.whiskerRight η (tensorLeft (Qh.obj P)) ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso C (.up ℤ)) :=
    (HomotopyCategory.KInjectives.localizerMorphism C)
      |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure _
        (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives
          H).isIso_of_isRightDerivedFunctor η I) _
  -- Derive the homotopy tensor-hom adjunction, then transport along Qh(P) ≅ K.
  exact ((HomotopyCategory.tensorHomAdjunction P).derived
    (HomotopyCategory.quasiIso C (.up ℤ)) (HomotopyCategory.quasiIso C (.up ℤ))
    (tensorLeftQhObjCounit P) η |>.ofNatIsoLeft
      ((tensoringLeft _).mapIso ((Qh (C := C)).objObjPreimageIso K))).isLeftAdjoint

end DerivedCategory
