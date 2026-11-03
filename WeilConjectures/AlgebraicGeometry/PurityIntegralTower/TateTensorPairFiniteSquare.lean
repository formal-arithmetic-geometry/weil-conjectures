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

/-- The finite scalar/Tate transition square on any compatible ordinary models.

Source: det-sp-scalar-extension-functor (3), ordinary Tate base change and exponent
independence; sk-thm-purity-transport, Step 1.
(blueprint: lem-sp-finite-tate-transition-model-square)
Proof: the derived finite transition theorem gives the square on the canonical
Tate single models. Compose with the lower chosen model. The assumed ordinary
model square, carried through the single functor, rewrites the result as the upper
chosen model followed by the single of the model transition. This is the same
single-transition assembly used for the previous presentation. -/
theorem finite_transition_square
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (m n : ℕ) (hmn : m ≤ n) (a : ZMod (ℓ ^ (m + 1)) →+* A) (r : ℤ)
    {Mb Ma : proEtaleRingModules T (proEtaleConstantRing T B)}
    (cb : scalarExtensionTateLine T ℓ B n
      (f.comp (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
        (ZMod (ℓ ^ (m + 1)))))) r ≅ Mb)
    (ca : scalarExtensionTateLine T ℓ B m (f.comp a) r ≅ Ma)
    (t : Mb ⟶ Ma)
    (ht : (scalarExtensionTateLevelIso T ℓ B m n hmn (f.comp a) r).hom ≫ ca.hom =
      cb.hom ≫ t) :
    (scalarExtensionFunctor f T).map
        ((DerivedCategory.singleFunctor _ 0).map
          (scalarExtensionTateLevelIso T ℓ A m n hmn a r).hom) ≫
      (finiteEvaluationModel f T ℓ m a r ca).hom =
    (finiteEvaluationModel f T ℓ n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) r cb).hom ≫
      (DerivedCategory.singleFunctor _ 0).map t := by
  have h := single_transition_assembly (DerivedCategory.singleFunctor _ 0)
    (scalarExtensionTateLevelIso T ℓ B m n hmn (f.comp a) r).hom cb.hom ca.hom t
    (scalarExtensionFunctorTateIso f T ℓ n
      (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
        (ZMod (ℓ ^ (m + 1))))) r).hom
    (scalarExtensionFunctorTateIso f T ℓ m a r).hom
    ((scalarExtensionFunctor f T).map
      ((DerivedCategory.singleFunctor _ 0).map
        (scalarExtensionTateLevelIso T ℓ A m n hmn a r).hom))
    (finiteTateTensor_transition_model f T ℓ m n hmn a r) ht
  simpa only [finiteEvaluationModel, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc] using h

end AlgebraicGeometry.ProEtale
