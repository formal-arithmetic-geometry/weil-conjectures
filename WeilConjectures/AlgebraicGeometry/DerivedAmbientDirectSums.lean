/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.AlgebraicGeometry.DerivedAmbientDirectSumsCofan
import WeilConjectures.AlgebraicGeometry.DerivedAmbientDirectSumsHomology

/-! # Direct sums in the derived category of module sheaves

Source: Stacks Project, Injectives, Lemma 07D9 (1)-(2), and Derived Categories of Schemes,
proof of Lemma 08DT.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

local instance instHasColimitsOfShape_derivedAmbientDirectSums (X : Scheme.{u}) (I : Type u) :
    HasColimitsOfShape (Discrete I)
      (CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  have : HasColimitsOfShape (Discrete I) C := inferInstance
  refine ⟨fun F ↦ ?_⟩
  have (n : ℤ) : HasColimit (F ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
    HasColimitsOfShape.has_colimit _
  exact ⟨⟨⟨_, HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩

/-- Termwise direct sums of any representatives give direct sums in `D(𝒪_X)`, and their
cohomology is canonically the direct sum of the cohomology sheaves.
Source: Stacks Project, Lemma 07D9 (1)-(2), and proof of Lemma 08DT. -/
theorem derivedAmbientDirectSums (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (I : Type u) (E : I → schemeDerivedCategory X)
    (K : I → CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (e : ∀ i : I, DerivedCategory.Q.obj (K i) ≅ E i) :
    Nonempty (IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ K))
      (fun i ↦ (e i).inv ≫ DerivedCategory.Q.map (Sigma.ι K i)))) ∧
    ∀ q : ℤ, IsIso (Sigma.desc (fun i ↦
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) q).map
          ((e i).inv ≫ DerivedCategory.Q.map (Sigma.ι K i)))) := by
  exact ⟨derivedAmbientDirectSumsCofan X I E K e,
    fun q ↦ derivedAmbientDirectSumsHomology X I E K e q⟩

end AlgebraicGeometry
