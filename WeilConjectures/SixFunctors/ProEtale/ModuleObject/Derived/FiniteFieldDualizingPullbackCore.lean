/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel

/-!
# Finite-stage core of the finite-field dualizing pullback

Source: latest blueprint `det-pd-biduality-coefficients.proof.md`, (i), finite-field paragraph
(blueprint: new-lem-sf-finite-field-dualizing-pullback-core).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedVariables false

universe u v w uC vC uD vD uB vB uB' vB'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The dualizing objects, counits and geometric pullback properties of the core. -/
structure FiniteFieldDualizingPullbackCore
    {C : Type uC} {D : Type uD} {B : Type uB} {B' : Type uB'}
    [Category.{vC} C] [Category.{vD} D] [Category.{vB} B] [Category.{vB'} B']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory B] [MonoidalCategory B']
    (constructible : ObjectProperty C) (ctf : ObjectProperty C) (ctfBar : ObjectProperty D)
    (G : C ⥤ D) [G.Monoidal] (H : B ⥤ B')
    (unitIso : H.obj (𝟙_ B) ≅ 𝟙_ B')
    (braid : ∀ K L : C, K ⊗ L ≅ L ⊗ K)
    (braidBar : ∀ K L : D, K ⊗ L ≅ L ⊗ K)
    (R : C ⥤ B) (Rbar : D ⥤ B') (alpha : R ⋙ H ⟶ G ⋙ Rbar)
    [MonoidalClosed C] [MonoidalClosed D] where
  W : C
  Wbar : D
  W_ctf : ctf W
  Wbar_ctf : ctfBar Wbar
  counit : R.obj W ⟶ 𝟙_ B
  counitBar : Rbar.obj Wbar ⟶ 𝟙_ B'
  represents : ∀ P : ctf.FullSubcategory,
    Function.Bijective (fun f : P.obj ⟶ W ↦ R.map f ≫ counit)
  representsBar : ∀ P : ctfBar.FullSubcategory,
    Function.Bijective (fun f : P.obj ⟶ Wbar ↦ Rbar.map f ≫ counitBar)
  symmetry : ∀ K L : C,
    Functor.LaxMonoidal.μ G K L ≫ G.map (braid K L).hom =
      (braidBar (G.obj K) (G.obj L)).hom ≫ Functor.LaxMonoidal.μ G L K
  preserves_ctf : ∀ K : ctf.FullSubcategory, ctfBar (G.obj K.obj)
  conservative : ∀ (K L : C) (f : K ⟶ L),
    constructible K → constructible L → IsIso (G.map f) → IsIso f
  exchange_iso : ∀ K : ctf.FullSubcategory, IsIso (alpha.app K.obj)
  dualizingIso : G.obj W ≅ Wbar
  counit_normalization : alpha.app W ≫ Rbar.map dualizingIso.hom ≫ counitBar =
    H.map counit ≫ unitIso.hom

end AlgebraicGeometry.ProEtale.CondensedRing
