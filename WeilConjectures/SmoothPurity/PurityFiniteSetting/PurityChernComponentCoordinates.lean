/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ProjectiveBundleFormula
import Mathlib.CategoryTheory.HomCongr

/-! # Hom coordinates of the specified projective-bundle morphism

Source: Stacks Tag 0FI5, projective-bundle basis before equation-chern-classes.
(blueprint: lem-pur-chern-component-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

private theorem finite_component_sum_bijective
    {C : Type v} [Category.{w} C] [Preadditive C]
    {J : Type} [Fintype J] (S : J → C) [HasBiproduct S]
    {Y : C} (f : (∐ S) ⟶ Y) [IsIso f] (K : C) :
    Function.Bijective (fun c : ∀ j, K ⟶ S j ↦
      ∑ j, c j ≫ Sigma.ι S j ≫ f) := by
  classical
  have hLift : Function.Bijective (fun c : ∀ j, K ⟶ S j ↦ biproduct.lift c) := by
    constructor
    · intro a b h
      funext j
      simpa only [biproduct.lift_π] using congrArg (fun g ↦ g ≫ biproduct.π S j) h
    · intro g
      refine ⟨fun j ↦ g ≫ biproduct.π S j, ?_⟩
      ext j
      simp only [biproduct.lift_π]
  let e := (Iso.refl K).homCongr (biproduct.isoCoproduct S ≪≫ asIso f)
  have h := e.bijective.comp hLift
  have heq : (fun c : ∀ j, K ⟶ S j ↦ e (biproduct.lift c)) =
      (fun c : ∀ j, K ⟶ S j ↦ ∑ j, c j ≫ Sigma.ι S j ≫ f) := by
    funext c
    simp only [e, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
      Iso.trans_hom, asIso_hom, biproduct.isoCoproduct_hom]
    rw [← Category.assoc, biproduct.lift_desc, Preadditive.sum_comp]
    simp only [Category.assoc]
  exact heq ▸ h

/-- Applying Hom(K,-) to the specified projective-bundle isomorphism gives the
bijection whose formula is the sum of the specified components. This statement
retains the actual morphism, rather than asserting an unrelated abstract bijection.
Source: Stacks Tag 0FI5, the projective-bundle basis used to define Chern classes.
Proof: finite biproduct lifting bijects coordinate families with Hom into the
coproduct. Postcompose with the projective-bundle isomorphism. The biproduct
lift-desc identity expands this composite as the displayed sum, and the coproduct
injection-desc identity identifies each component with projectiveBundleComponent.
(blueprint: lem-pur-chern-component-coordinates). -/
theorem projectiveBundleComponentSum_bijective (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) (n : ℕ) (G : ProjectiveBundleTautologicalSystem.{u} n)
    (T : Scheme.{u}) (F : T.Modules) (hF : projectiveBundleRank T n F)
    (a : T ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))) :
    Function.Bijective
      (fun c : ∀ j : Fin (n + 1), K ⟶ P.projectiveBundleSummand T j.val ↦
        ∑ j : Fin (n + 1), c j ≫
          P.projectiveBundleComponent t a (G.bundle T F hF) (G.invertible T F hF) j.val) := by
  have := (P.projectiveBundleFormula t n G T F hF a).1
  have h := finite_component_sum_bijective
    (fun j : Fin (n + 1) ↦ P.projectiveBundleSummand T j.val)
    (P.projectiveBundleMap t n a (G.bundle T F hF) (G.invertible T F hF)) K
  simpa only [projectiveBundleMap, Sigma.ι_desc, Category.assoc] using h

end WeilConjectures.PurityFiniteSetting
