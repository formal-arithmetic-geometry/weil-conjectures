/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.AlgebraicGeometry.AffineHomComplexEvaluationD
import WeilConjectures.Algebra.Homology.HomComplexUnitIso

/-! # Termwise affine Hom evaluation

## References

* Stacks Project, Tags 0BUZ, 0BV0, 0AX3
-/

@[expose] public section
universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace AlgebraicGeometry
/-- The affine Hom comparison and evaluation identity hold before localization, on
all unbounded complexes (Stacks, Tags 0BUZ, 0BV0, 0AX3). -/
theorem affine_hom_complex_evaluation
    {Y X : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
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
    ∃ e : (homComplexFunctor (R := Y.toRingedSpace.sheaf)).obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _,
      ∀ I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      ∃ d : (((SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).mapHomologicalComplex
            (.up ℤ)).obj ((H.mapHomologicalComplex (.up ℤ)).obj I)) ≅
          homComplex (R := Y.toRingedSpace.sheaf)
            ((CochainComplex.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                ((Scheme.Modules.pushforward f).obj
                  (SheafOfModules.unit X.ringCatSheaf))) I,
        d.hom ≫ ((homComplexFunctor (R := Y.toRingedSpace.sheaf)).map
          (((CochainComplex.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
              (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).op)).app I ≫
            e.hom.app I =
              ((NatTrans.mapHomologicalComplex adj₀.counit (.up ℤ)).app I) := by
  classical
  obtain ⟨e⟩ := CategoryTheory.homComplex_unit_iso
    (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
  refine ⟨e, ?_⟩
  exact affine_hom_complex_d f H iH adj₀ h_eval e

end AlgebraicGeometry
