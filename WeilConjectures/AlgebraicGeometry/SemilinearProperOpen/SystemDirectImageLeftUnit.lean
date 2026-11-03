/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import all WeilConjectures.SixFunctors.AmbientCompositor.Operations.AmbientAdjunctionCompositorNormalization

/-! # Left unit for the semilinear direct-image compositor

Source: Stacks 07A7 and the ordinary adjunction compositor normalization.
(blueprint: lem-pur-system-direct-image-left-unit). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.proofsInPublic true
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)

/-- The specified proper compositor with an identity first factor is the image
of the specified direct-image unitor.
Source: Stacks 07A7, adjunction conjugation and the ordinary pullback unit law.
(blueprint: lem-pur-system-direct-image-left-unit).
Proof: specialize the ambient direct-image unit theorem to the existing whole-system
operations. Its pullback coherence is the localization of ordinary pullback coherence.
The ambient compositor is the conjugate of exactly the published pComp, and its
identity comparison is exactly sId. Substituting these identifications gives the equation. -/
theorem sComp_left_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : SemilinearProperOpen.Derived C τ X) :
    (SemilinearProperOpen.sComp C τ (𝟙 X) f).hom.app M ≫
        (eqToIso (congrArg (SemilinearProperOpen.R C τ) (Category.id_comp f))).hom.app M =
      (SemilinearProperOpen.R C τ f).map ((SemilinearProperOpen.sId C τ X).hom.app M) := by
  have h := (WeilConjectures.AmbientCompositor.s_unital
    (WeilConjectures.AmbientCompositor.systems C τ)
    (WeilConjectures.AmbientCompositor.descend_pull_coherence _
      (WeilConjectures.AmbientCompositor.system_ordinary_pull_coherence C τ)) f M).1
  simp only [WeilConjectures.AmbientCompositor.c_eq,
    WeilConjectures.AmbientCompositor.pComp_eq,
    WeilConjectures.AmbientCompositor.Operations.sId,
    WeilConjectures.AmbientCompositor.Operations.pId,
    WeilConjectures.AmbientCompositor.systems,
    WeilConjectures.AmbientCompositor.Operations.adjunction,
    WeilConjectures.AmbientCompositor.Operations.P,
    WeilConjectures.AmbientCompositor.Operations.S,
    SemilinearProperOpen.sComp, SemilinearProperOpen.sId,
    SemilinearProperOpen.pId, SemilinearProperOpen.pComp,
    SemilinearProperOpen.adj, SemilinearProperOpen.R] at h ⊢
  with_unfolding_all exact h
end AlgebraicGeometry.ProEtale.SemilinearProperOpen
