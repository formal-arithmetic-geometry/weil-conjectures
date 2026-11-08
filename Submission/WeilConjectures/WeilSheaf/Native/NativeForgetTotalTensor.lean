/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalizedRestrictionDescent
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorCoequalizer
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Mod.MapIhom
public import Submission.WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatForget
import Mathlib.Algebra.Homology.BifunctorFlip
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Forgetting the Weil structure of native total tensor complexes

The native tensor product of pro-étale Weil sheaves `B ⊗ A` has underlying sheaf the relative
tensor product `(Mod.tensorLeft B).obj A` of the underlying `ℓ`-adic sheaves, which is the monoidal
tensor product `A ⊗ B` of `ℓ`-adic sheaves (`CategoryTheory.Mod.relativeTensorRightIso`). This file
records the resulting comparison of the native total tensor complex with the tensor product of
complexes of `ℓ`-adic sheaves after forgetting the Weil structures.

## Main definitions

* `AlgebraicGeometry.ProEtaleWeilSheaf.nativeForgetTensorIso`: forgetting the Weil structure of
  the native tensor product of sheaves gives the tensor product of `ℓ`-adic sheaves.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [Abelian C] [IsGrothendieckAbelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

omit [MonoidalPreadditive C] in
/-- The identification `(Mod.tensorLeft N).obj M ≅ M ⊗ N` is natural in `N`. -/
lemma tensorLeftMap_app_comp_relativeTensorRightIso_hom_app {N N' : Mod C R} (g : N ⟶ N')
    (M : Mod C R) :
    (tensorLeftMap g).app M ≫ (relativeTensorRightIso N').hom.app M =
      (relativeTensorRightIso N).hom.app M ≫ M ◁ g := by
  apply tensorLeft_hom_ext N M
  have h₁ : tensorLeftπ N M ≫ (relativeTensorRightIso N).hom.app M = relativeTensorπ M N := by
    simp [relativeTensorRightIso, tensorLeftπ, relativeTensorCofork]
  have h₂ : tensorLeftπ N' M ≫ (relativeTensorRightIso N').hom.app M = relativeTensorπ M N' := by
    simp [relativeTensorRightIso, tensorLeftπ, relativeTensorCofork]
  rw [reassoc_of% h₁, ← Category.assoc, tensorLeftπ_tensorLeftMap_app, Category.assoc, h₂]
  apply Mod.hom_ext
  exact (tensorObjπ_whiskerLeft g).symm

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- The underlying map of the native tensor product with a morphism, in the fixed variable, is
the tensor product of the underlying morphism of `ℓ`-adic sheaves. -/
lemma nativeTensorMap_app_hom_f {A B : ProEtaleWeilSheaf k₀ l X} (f : A ⟶ B)
    (Q : ProEtaleWeilSheaf k₀ l X) :
    ((nativeTensorMap k₀ l X f).app Q).hom.f = (Mod.tensorLeftMap f.hom.f).app Q.carrier := by
  change ((conjugateEquiv (Mod.ihomAdjunction B.carrier)
    (Mod.ihomAdjunction A.carrier)).symm (Mod.ihomMap f.hom.f)).app Q.carrier = _
  rw [Mod.ihomMap, Equiv.symm_apply_apply]

/-- Naturality of the forgetful comparison of native tensor products. -/
lemma nativeForgetTensor_naturality {P T P' T' : ProEtaleWeilSheaf k₀ l X} (f : P ⟶ P')
    (g : T ⟶ T') :
    ((tensorFunctor k₀ l X T).map f ≫ (nativeTensorMap k₀ l X g).app P').hom.f ≫
        (Mod.relativeTensorRightIso T'.carrier).hom.app P'.carrier =
      (Mod.relativeTensorRightIso T.carrier).hom.app P.carrier ≫ (f.hom.f ⊗ₘ g.hom.f) := by
  rw [Endofunctor.IsoAlgebra.comp_hom_f, nativeTensorMap_app_hom_f, Category.assoc,
    Mod.tensorLeftMap_app_comp_relativeTensorRightIso_hom_app]
  change (Mod.tensorLeft T.carrier).map f.hom.f ≫ _ ≫ _ = _
  rw [← Category.assoc, (Mod.relativeTensorRightIso T.carrier).hom.naturality f.hom.f,
    Category.assoc, MonoidalCategory.tensorHom_def]
  rfl

/-- Forgetting the Weil structure of the native tensor product `B ⊗ A`, with `A` the first
variable, gives the tensor product `A ⊗ B` of the underlying `ℓ`-adic sheaves. -/
def nativeForgetTensorIso :
    Functor.uncurry.obj (nativeTensorBifunctor k₀ l X).flip ⋙
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
        Functor.uncurry.obj (curriedTensor
          (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :=
  NatIso.ofComponents (fun PT ↦ (Mod.relativeTensorRightIso PT.2.carrier).app PT.1.carrier)
    (by
      rintro ⟨P, T⟩ ⟨P', T'⟩ ⟨f, g⟩
      exact nativeForgetTensor_naturality k₀ l X f g)

/-- `AlgebraicGeometry.ProEtaleWeilSheaf.nativeForgetTensorIso`, as a morphism of bifunctors. -/
def nativeForgetTensorNatTrans :
    (Functor.postcompose₂.obj
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))).obj
        (nativeTensorBifunctor k₀ l X).flip ⟶
      (((Functor.whiskeringLeft₂ _).obj
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))).obj
          (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X))).obj
        (curriedTensor (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) where
  app P :=
    { app T := (nativeForgetTensorIso k₀ l X).hom.app (P, T)
      naturality T T' g := by
        simpa using (nativeForgetTensorIso k₀ l X).hom.naturality (Prod.mkHom (𝟙 P) g) }
  naturality P P' f := by
    refine NatTrans.ext (funext fun T ↦ ?_)
    simpa using (nativeForgetTensorIso k₀ l X).hom.naturality (Prod.mkHom f (𝟙 T))

instance (P T : ProEtaleWeilSheaf k₀ l X) :
    IsIso (((nativeForgetTensorNatTrans k₀ l X).app P).app T) :=
  inferInstanceAs (IsIso ((nativeForgetTensorIso k₀ l X).hom.app (P, T)))

omit [Fact (ringChar k₀ ≠ l)] in
/-- The tensor product `(Mod.tensorLeft P).obj N` of `ℓ`-adic sheaves is the monoidal tensor
product `N ⊗ P`, naturally in both variables. -/
def ordinaryTensorBifunctorFlipIso (Y : Scheme.{u}) :
    (ordinaryTensorBifunctor l Y).flip ≅ curriedTensor (ProEtale.AdicSheaf l Y) :=
  NatIso.ofComponents
    (fun N ↦ NatIso.ofComponents (fun P ↦ (Mod.relativeTensorRightIso P).app N)
      (fun {P P'} g ↦ by
        change (Mod.tensorLeftMap g).app N ≫ (Mod.relativeTensorRightIso P').hom.app N = _
        rw [Mod.tensorLeftMap_app_comp_relativeTensorRightIso_hom_app]
        rfl))
    (fun {N N'} f ↦ by
      refine NatTrans.ext (funext fun P ↦ ?_)
      exact (Mod.relativeTensorRightIso P).hom.naturality f)

end AlgebraicGeometry.ProEtaleWeilSheaf
