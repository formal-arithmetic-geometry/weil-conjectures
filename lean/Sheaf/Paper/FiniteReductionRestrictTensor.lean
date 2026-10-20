/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.FiniteReductionSystem
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange

/-! Restriction of sheaf scalar extension as tensor by the target ring. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteReduction

section Site
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B]

/-- Restricting a sheafified scalar extension is tensoring with the constant target
ring, regarded as a module over the source. Source: Stacks Tag 06YY.
(blueprint: lem-pur-finite-reduction-restrict-tensor). -/
def extend_restrict_tensor (f : A →+* B) :
    extend J f ⋙ Sheaf.restrictScalars J f ≅
      tensorRight ((constantSheaf J (ModuleCat.{u + 1} A)).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))) := by
  letI : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} f) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} f)
  let S := sheafToPresheaf J (ModuleCat.{u + 1} A)
  let W := (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.extendScalars.{u + 1} f)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} B)
  let a := presheafToSheaf J (ModuleCat.{u + 1} A)
  let U := Sheaf.restrictScalars J f
  let X := (Functor.const Cᵒᵖ).obj ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))
  exact Functor.associator S (W ⋙ a') U ≪≫
    Functor.isoWhiskerLeft S (Functor.associator W a' U) ≪≫
    Functor.isoWhiskerLeft S (Functor.isoWhiskerLeft W
      (sheafComposeNatIso J (ModuleCat.restrictScalars f)
        (sheafificationAdjunction J (ModuleCat.{u + 1} B))
        (sheafificationAdjunction J (ModuleCat.{u + 1} A))).symm) ≪≫
    Functor.isoWhiskerLeft S (Functor.associator W _ a).symm ≪≫
    Functor.isoWhiskerLeft S (Functor.isoWhiskerRight
      (Functor.whiskeringRightObjCompIso _ _ ≪≫
        (Functor.whiskeringRight _ _ _).mapIso
          (ModuleCat.extendScalarsCompRestrictScalarsIso f) ≪≫
        whiskeringRightTensorRightIso _) a) ≪≫
    Functor.isoWhiskerLeft S (Sheaf.presheafToSheafCompTensorRightIso X).symm ≪≫
    (Functor.associator S a (tensorRight (a.obj X))).symm ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} A)).counit)
      (tensorRight (a.obj X)) ≪≫ Functor.leftUnitor _

end Site
end AlgebraicGeometry.FiniteReduction
