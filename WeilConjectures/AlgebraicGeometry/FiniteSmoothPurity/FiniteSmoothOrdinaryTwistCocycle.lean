/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import all WeilConjectures.AlgebraicGeometry.P1.P1KummerScalarEndpointComposition
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothRootDerivedComposition
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothZeroTwistComposition

/-! # Ordinary quotient coherence for normalized root tensors

Source: smooth-purity reduction compatibilities, part (3).
(blueprint: lem-pur-finite-smooth-ordinary-twist-cocycle).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem quotient_comp (ell : ℕ) {r m n : ℕ}
    (hmr : m ≤ r) (hnm : n ≤ m) :
    FiniteReduction.quotient.{u} ell (hnm.trans hmr) =
      (FiniteReduction.quotient ell hnm).comp (FiniteReduction.quotient ell hmr) := by
  exact RingHom.ext (fun x ↦
    congrArg (fun y : ZMod (ell ^ n) ↦ (⟨⟨y⟩⟩ : FiniteReduction.Coeff.{u} ell n))
      (DFunLike.congr_fun
        (Subsingleton.elim
          (ZMod.castHom (pow_dvd_pow ell (hnm.trans hmr)) (ZMod (ell ^ n)))
          ((ZMod.castHom (pow_dvd_pow ell hnm) (ZMod (ell ^ n))).comp
            (ZMod.castHom (pow_dvd_pow ell hmr) (ZMod (ell ^ m))))) x.down.down))

private theorem tensor_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    (TA : C × C ⥤ C) (TB : D × D ⥤ D) (TC : E × E ⥤ E)
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (α : F ⋙ G ≅ H)
    (δF : TA ⋙ F ≅ F.prod F ⋙ TB) (δG : TB ⋙ G ≅ G.prod G ⋙ TC)
    (δH : TA ⋙ H ≅ H.prod H ⋙ TC)
    {X U : C} {Y V : D} {Z W : E}
    (p : F.obj X ⟶ Y) (q : F.obj U ⟶ V)
    (s : G.obj Y ⟶ Z) (t : G.obj V ⟶ W)
    (c : H.obj X ⟶ Z) (d : H.obj U ⟶ W)
    (hp : G.map p ≫ s = α.hom.app X ≫ c)
    (hq : G.map q ≫ t = α.hom.app U ≫ d)
    (hδ : G.map (δF.hom.app (X, U)) ≫ δG.hom.app (F.obj X, F.obj U) ≫
      TC.map (Prod.mkHom (α.hom.app X) (α.hom.app U)) =
      α.hom.app (TA.obj (X, U)) ≫ δH.hom.app (X, U)) :
    G.map (δF.hom.app (X, U) ≫ TB.map (Prod.mkHom p q)) ≫ δG.hom.app (Y, V) ≫
      TC.map (Prod.mkHom s t) =
    α.hom.app (TA.obj (X, U)) ≫ δH.hom.app (X, U) ≫ TC.map (Prod.mkHom c d) := by
  have hn := δG.hom.naturality (show (F.obj X, F.obj U) ⟶ (Y, V) from Prod.mkHom p q)
  change G.map (TB.map (Prod.mkHom p q)) ≫ δG.hom.app (Y, V) =
    δG.hom.app (F.obj X, F.obj U) ≫ TC.map (Prod.mkHom (G.map p) (G.map q)) at hn
  rw [G.map_comp, Category.assoc, reassoc_of% hn, ← TC.map_comp]
  change _ ≫ _ ≫ TC.map (Prod.mkHom (G.map p ≫ s) (G.map q ≫ t)) = _
  rw [hp, hq]
  change _ ≫ _ ≫ TC.map (Prod.mkHom (α.hom.app X) (α.hom.app U) ≫ Prod.mkHom c d) = _
  rw [TC.map_comp]
  simpa only [Category.assoc] using congrArg (· ≫ TC.map (Prod.mkHom c d)) hδ

set_option linter.unusedVariables false in
end AlgebraicGeometry.Etale.FiniteSmoothPurity
