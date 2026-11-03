/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.CondensedTateIntegralTowerData
import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.TateTensorFiniteTransition
import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.CondensedTateIntegralTowerData
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! Single-model transport of the ordinary finite Tate transition square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local irreducible] HasDerivedCategory.standard Functor.leftAdjoint
  SheafOfModules.monoidalCategory completedAdicDerivedChange finiteModelIso

end AlgebraicGeometry.Scheme.PurityIntegralTower

namespace AlgebraicGeometry.ProEtale

/-- The canonical derived Tate comparison followed by an ordinary model isomorphism.
Source: det-sp-scalar-extension-functor (3).
(blueprint: lem-sp-finite-tate-transition-model-square) -/
def finiteEvaluationModel
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) (r : ℤ)
    {M : proEtaleRingModules T (proEtaleConstantRing T B)}
    (c : scalarExtensionTateLine T ℓ B n (f.comp a) r ≅ M) :
    (scalarExtensionFunctor f T).obj
        ((DerivedCategory.singleFunctor _ 0).obj (scalarExtensionTateLine T ℓ A n a r)) ≅
      (DerivedCategory.singleFunctor _ 0).obj M :=
  scalarExtensionFunctorTateIso f T ℓ n a r ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso c

private theorem single_transition_assembly
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y u v : C} (f : x ⟶ y) (cb : x ⟶ u) (ca : y ⟶ v) (t : u ⟶ v)
    {Mb Ma : D} (pb : Mb ⟶ F.obj x) (pa : Ma ⟶ F.obj y) (δ : Mb ⟶ Ma)
    (hmodel : δ ≫ pa = pb ≫ F.map f) (hord : f ≫ ca = cb ≫ t) :
    δ ≫ pa ≫ F.map ca = pb ≫ F.map cb ≫ F.map t := by
  calc
    δ ≫ pa ≫ F.map ca = pb ≫ F.map f ≫ F.map ca := by
      rw [reassoc_of% hmodel]
    _ = pb ≫ F.map cb ≫ F.map t := by
      rw [← F.map_comp, hord, F.map_comp]

end AlgebraicGeometry.ProEtale
