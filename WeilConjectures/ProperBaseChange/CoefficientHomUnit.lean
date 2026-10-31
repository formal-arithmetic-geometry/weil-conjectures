/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.Algebra.Homology.LocalizationCech.ExtendedLocalizationCechSupplement
import WeilConjectures.Algebra.Homology.ProperBaseChange.RestrictedCoefficientHomComplexSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # The coefficient-Hom unit for the ring in degree zero

Source: Stacks Project, Algebraization, Tag 099I, first arrow of the final composite.
(blueprint: lem-weil-pbc-coefficient-hom-unit).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

end ModuleCat

namespace PresheafOfModules

variable {C : Type u} [SmallCategory C]
  {R B : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : R ⟶ B)

end PresheafOfModules

namespace SheafOfModules

attribute [local irreducible] homComplexFunctor homComplexIsLimit

end SheafOfModules

namespace SheafOfModules

attribute [local irreducible] homComplexFunctor

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem sheaf_comp_apply
    {S : Sheaf J RingCat.{u}} {M N P : SheafOfModules.{u} S}
    (f : M ⟶ N) (g : N ⟶ P) (U : Cᵒᵖ) (m : M.val.obj U) :
    (((f ≫ g).val.app U).hom m) = (g.val.app U).hom ((f.val.app U).hom m) := rfl

variable (H :
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))ᵒᵖ ×
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
        SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
  (i : H ⋙ restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) ≅
    (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).op.prod
      (𝟭 _) ⋙ Functor.uncurry.obj (homFunctor R))
  (haction : ∀ (M : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
          (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
          (U : C)
          (b : ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj.obj (op U))
          (h : (H.obj (op M, N)).val.obj (op U)) (W : Over U)
          (m : M.val.obj (op W.left)),
          (((i.hom.app (op M, N)).val.app (op U)).hom
            (@SMul.smul _ _ ((H.obj (op M, N)).val.obj (op U)).isModule.toSMul b h)).app (op W) m =
            (((i.hom.app (op M, N)).val.app (op U)).hom h).app (op W)
              (@SMul.smul _ _ (M.val.obj (op W.left)).isModule.toSMul
                (B.obj.map W.hom.op b) m))

attribute [local irreducible] unitRawMap unitRawSection

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
attribute [local irreducible] unitBase

attribute [local irreducible] homObjMap homObjUnitIso

include haction in
end SheafOfModules

namespace SheafOfModules

variable {A E : Type u} [Category.{v} A] [Category.{v} E]
    [Preadditive A] [HasZeroMorphisms E]
    (r : A ⥤ E) [r.PreservesZeroMorphisms] (H : Aᵒᵖ × E ⥤ A)
    (L : CochainComplex A ℤ)
    (η : ∀ M : A, M ⟶ H.obj (op (L.X 0), r.obj M))
    (hη : ∀ {M N : A} (f : M ⟶ N),
      f ≫ η N = η M ≫ H.map (X := (op (L.X 0), r.obj M))
        (Y := (op (L.X 0), r.obj N)) ((𝟙 (L.X 0)).op, r.map f))

omit [HasZeroMorphisms E] [r.PreservesZeroMorphisms] in
omit [HasZeroMorphisms E] [r.PreservesZeroMorphisms] in
include hη in
include hη in
end SheafOfModules

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency true


attribute [local irreducible] homComplexFunctor homComplexIsLimit
attribute [local irreducible] sheafCompose SheafOfModules.restrictScalars
  SheafOfModules.coefficientHomObjComparisonHom SheafOfModules.genericUnitComponent

attribute [local irreducible] ringedHomUnitEvaluationIso
  ringedHomUnitFunctorEvaluationIso homComplexUnitEvaluation homComplexπ

-- Keep the propositional instance witnesses small at the concrete interface.
set_option maxHeartbeats 800000 in
-- The statement and its normalization compare several chosen Hom-complex constructions.
end CategoryTheory
