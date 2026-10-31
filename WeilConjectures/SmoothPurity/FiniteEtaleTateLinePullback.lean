/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback

/-! # Generator-normalized pullback of finite Tate lines
Source: Stacks Project, Etale Cohomology, Section 03PK. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u u'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

private noncomputable def muHomEquiv (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleMuModulePresheaf T N ⟶
      P.obj ⋙ ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)) ≃
    (T.rootsOfUnitySheaf N ⟶
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) where
  toFun f := ⟨{
    app := fun U ↦ AddCommGrpCat.ofHom (f.app U).hom.toAddMonoidHom
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.naturality g) x }⟩
  invFun f := {
    app := fun U ↦ ModuleCat.ofHom
      (X := finiteEtaleMuModuleObj T N U)
      (Y := (ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)).obj (P.obj.obj U))
      (AddMonoidHom.toZModLinearMap N
        (M := finiteEtaleMuModuleObj T N U)
        (M₁ := (ModuleCat.restrictScalars (finiteEtaleTwistScalar N A hA)).obj (P.obj.obj U))
        (f.hom.app U).hom)
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
  left_inv f := by ext U x; rfl
  right_inv f := by ext U x; rfl

private noncomputable def lineHomEquiv (T : Scheme.{u}) (N : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (N : A) = 0) (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (finiteEtaleTateLine T N A hA ⟶ P) ≃
    (T.rootsOfUnitySheaf N ⟶
      (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj P) :=
  ((sheafificationAdjunction T.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ P).trans
    ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).whiskerRight
      T.Etaleᵒᵖ).homEquiv _ P.obj).trans (muHomEquiv T N A hA P))

private lemma lineHomEquiv_generator (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (P : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : finiteEtaleTateLine T N A hA ⟶ P) (U : T.Etaleᵒᵖ)
    (z : (T.rootsOfUnitySheaf N).obj.obj U) :
    (lineHomEquiv T N A hA P f).hom.app U z =
      f.hom.app U (finiteEtaleTateOneGenerator A N T hA U 1 z) := by
  dsimp [lineHomEquiv, muHomEquiv]
  change ((ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
      (finiteEtaleTwistScalar N A hA)).homEquiv _ _
        ((toSheafify T.smallEtaleTopology _ ≫ f.hom).app U)) z = _
  rfl

end AlgebraicGeometry.Scheme
