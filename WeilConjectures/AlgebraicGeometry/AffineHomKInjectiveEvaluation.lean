/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.AlgebraicGeometry.AffineHomComplexEvaluation
import WeilConjectures.AlgebraicGeometry.DerivedSingleHomEvaluation

/-! # Evaluation of affine Hom on K-injective complexes

Source: Stacks Project, duality.tex, Tags 0BUZ, 0BV0 and 0AX3.
-/

@[expose] public section

universe u wY

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The termwise affine Hom comparison on K-injective targets respects evaluation.
This statement involves only the underived adjunction, with no supplied derived functors.

Source: Stacks Project, duality.tex, Tags 0BUZ, 0BV0 and 0AX3. -/
theorem affine_hom_kInjective_evaluation
    {Y X : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (H : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
      [H.Additive]
      (iH : H ⋙ SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ≅
        (SheafOfModules.homFunctor Y.sheaf).obj
          (op ((SheafOfModules.restrictScalars
            (R := moduleRings Y.toRingedSpace)
            (R' := moduleRings (directImageAlgebraSpace f))
            ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).obj
              (SheafOfModules.unit (moduleRings (directImageAlgebraSpace f))))))
      (adj₀ : SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩ ⊣ H)
    (h_eval : ∀ (F : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (U : Y.Opens)
          (φ : (H.obj F).val.obj (op U)),
        ((adj₀.counit.app F).val.app (op U)).hom φ =
          ((((iH.hom.app F).val.app (op U)).hom φ).app (op (Over.mk (𝟙 U)))).hom
            (1 : (moduleRings (directImageAlgebraSpace f)).obj.obj (op U))) :
    ∃ j : (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _,
      ∀ (I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (_ : I.IsKInjective),
      ∃ c : DerivedCategory.Q.obj
          (((SheafOfModules.restrictScalars
            (R := moduleRings Y.toRingedSpace)
            (R' := moduleRings (directImageAlgebraSpace f))
            ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).mapHomologicalComplex
              (.up ℤ)).obj ((H.mapHomologicalComplex (.up ℤ)).obj I)) ≅
          (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
            (op ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))),
              DerivedCategory.Q.obj I),
        c.hom ≫ (derivedInternalHom (Opens.grothendieckTopology Y)
            Y.toRingedSpace.sheaf).map
          (((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
              (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).op,
            𝟙 (DerivedCategory.Q.obj I)) ≫
          j.hom.app (DerivedCategory.Q.obj I) =
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex adj₀.counit (.up ℤ)).app I) := by
  refine (affine_hom_complex_evaluation f H iH adj₀ h_eval).elim fun e he ↦ ?_
  refine (derived_single_hom_evaluation Y e).elim fun j hj ↦ ?_
  refine ⟨j, ?_⟩
  intro I hI
  refine (he I).elim fun d hd ↦ ?_
  refine (hj _ (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) I hI).elim
    fun c hc ↦ ?_
  refine ⟨DerivedCategory.Q.mapIso d ≪≫ c, ?_⟩
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [hc, ← Functor.map_comp, hd]

end AlgebraicGeometry
