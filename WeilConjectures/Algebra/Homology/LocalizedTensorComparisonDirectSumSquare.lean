/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import WeilConjectures.Algebra.Homology.LocalizedComparisonCoproductSource
import Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.AlgebraicGeometry.DerivedAmbientDirectSumsHomology
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits

/-!
# Direct-sum square for localized tensor comparisons

## References

* Stacks Project, Tags 0DJA(1) and 0BYJ
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The localized comparison on a direct sum is conjugate to the sum of the comparisons. -/
theorem exists_localizedTensorComparison_direct_sum_square
    {I : Type u} (U : I → CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ∀ j, BaseDerivedTensorCohomologyModel R A B (U j ⊗ Q) C)
    (mS : BaseDerivedTensorCohomologyModel R A B ((∐ U) ⊗ Q) C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    let α := fun j ↦ (m j).localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F (U j) Q).inv ≫ (F.obj (U j) ◁ t)) i
    ∃ (e : (∐ fun j ↦ (extendScalars (algebraMap (A ⊗[R] B) C)).obj
        ((m j).cohomology i)) ≅
      (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mS.cohomology i))
      (d : (∐ fun j ↦ (F.obj (U j) ⊗ N).homology i) ≅
        (F.obj (∐ U) ⊗ N).homology i),
      Limits.Sigma.map α ≫ d.hom = e.hom ≫
        (mS.localizedComparison i ≫ HomologicalComplex.homologyMap
          ((Functor.Monoidal.μIso F (∐ U) Q).inv ≫ (F.obj (∐ U) ◁ t)) i) := by
  classical
  dsimp only
  let F := (extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)
  have (X : ModuleCat.{u} A) : PreservesColimitsOfShape (Discrete I) (tensorRight X) :=
    ⟨fun {K} ↦ inferInstance⟩
  have : PreservesColimitsOfShape (Discrete I) (tensorRight Q) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete I)
      ((curriedTensor (ModuleCat.{u} A)).map₂CochainComplex.flip.obj Q))
  have hs : IsColimit (Cofan.mk ((∐ U) ⊗ Q) (fun j ↦ Sigma.ι U j ▷ Q)) :=
    isColimitOfHasCoproductOfPreservesColimit (tensorRight Q) U
  obtain ⟨e, he⟩ := exists_localizedComparison_coproduct_source R A B C
    (fun j ↦ U j ⊗ Q) ((∐ U) ⊗ Q) (fun j ↦ Sigma.ι U j ▷ Q) hs m mS i
  have hshort := AlgebraicGeometry.shortComplexHomologyColimit (ModuleCat.{u} C)
    (Discrete I)
  have := AlgebraicGeometry.complexHomologyColimit (ModuleCat.{u} C) (Discrete I) hshort i
  have (X : ModuleCat.{u} C) : PreservesColimitsOfShape (Discrete I) (tensorRight X) :=
    ⟨fun {K} ↦ inferInstance⟩
  have : PreservesColimitsOfShape (Discrete I) (tensorRight N) :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete I)
      ((curriedTensor (ModuleCat.{u} C)).map₂CochainComplex.flip.obj N))
  let T := F ⋙ tensorRight N ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) i
  have : PreservesColimitsOfShape (Discrete I) T := by infer_instance
  let d : (∐ fun j ↦ (F.obj (U j) ⊗ N).homology i) ≅
      (F.obj (∐ U) ⊗ N).homology i := (PreservesCoproduct.iso T U).symm
  have hd (j : I) : Sigma.ι (fun j ↦ (F.obj (U j) ⊗ N).homology i) j ≫ d.hom =
      HomologicalComplex.homologyMap (F.map (Sigma.ι U j) ▷ N) i := by
    change Sigma.ι _ j ≫ sigmaComparison T U = T.map (Sigma.ι U j)
    exact Sigma.ι_comp_desc _ _
  refine ⟨e, d, ?_⟩
  apply Sigma.hom_ext
  intro j
  have hn :
      F.map (Sigma.ι U j ▷ Q) ≫
        (Functor.Monoidal.μIso F (∐ U) Q).inv ≫ (F.obj (∐ U) ◁ t) =
      (Functor.Monoidal.μIso F (U j) Q).inv ≫
        (F.obj (U j) ◁ t) ≫ (F.map (Sigma.ι U j) ▷ N) := by
    simp only [Functor.Monoidal.μIso_inv]
    rw [← Functor.OplaxMonoidal.δ_natural_left_assoc]
    rw [← whisker_exchange]
  simp only [Category.assoc, Sigma.ι_map_assoc]
  erw [hd, reassoc_of% he j]
  simp only [← HomologicalComplex.homologyMap_comp, Category.assoc]
  rw [hn]


end ModuleCat
