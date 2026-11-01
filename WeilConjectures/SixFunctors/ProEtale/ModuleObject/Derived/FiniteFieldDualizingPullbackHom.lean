/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteFieldDualizingPullbackCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-!
# Internal-Hom comparison for the finite-field dualizing pullback

Source: latest blueprint `det-pd-biduality-coefficients.proof.md`, (i), finite-field paragraph
(blueprint: new-lem-sf-finite-field-dualizing-pullback-hom).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedVariables false

universe u v uC vC uD vD uB vB uB' vB'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The internal-Hom conclusions over a given core: `β` is invertible, and the supplied comparison
is invertible, contravariantly natural and compatible with evaluation. -/
structure FiniteFieldDualizingPullbackHomData
    {C : Type uC} {D : Type uD} {B : Type uB} {B' : Type uB'}
    [Category.{vC} C] [Category.{vD} D] [Category.{vB} B] [Category.{vB'} B']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory B] [MonoidalCategory B']
    [MonoidalClosed C] [MonoidalClosed D]
    (constructible : ObjectProperty C) (ctf : ObjectProperty C) (ctfBar : ObjectProperty D)
    (G : C ⥤ D) [G.Monoidal] (H : B ⥤ B')
    (unitIso : H.obj (𝟙_ B) ≅ 𝟙_ B')
    (braid : ∀ K L : C, K ⊗ L ≅ L ⊗ K)
    (braidBar : ∀ K L : D, K ⊗ L ≅ L ⊗ K)
    (R : C ⥤ B) (Rbar : D ⥤ B') (alpha : R ⋙ H ⟶ G ⋙ Rbar)
    (core : FiniteFieldDualizingPullbackCore constructible ctf ctfBar G H unitIso braid braidBar
      R Rbar alpha)
    (comparison : ∀ K : C, G.obj ((ihom K).obj core.W) ⟶
      (ihom (G.obj K)).obj core.Wbar) where
  beta_iso : ∀ K : ctf.FullSubcategory,
    IsIso ((Functor.LaxMonoidal.ihomComparison G K.obj).natTrans.app core.W)
  comparison_iso : ∀ K : ctf.FullSubcategory, IsIso (comparison K.obj)
  comparison_natural : ∀ (K L : ctf.FullSubcategory) (f : L.obj ⟶ K.obj),
    G.map ((MonoidalClosed.pre f).app core.W) ≫ comparison L.obj =
      comparison K.obj ≫ (MonoidalClosed.pre (G.map f)).app core.Wbar
  evaluation : ∀ K : ctf.FullSubcategory,
    G.obj K.obj ◁ comparison K.obj ≫ (ihom.ev (G.obj K.obj)).app core.Wbar =
      Functor.LaxMonoidal.μ G K.obj _ ≫ G.map ((ihom.ev K.obj).app core.W) ≫
        core.dualizingIso.hom

end AlgebraicGeometry.ProEtale.CondensedRing
