/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
import all Sheaf.AlgebraicGeometry.CoherentFormalModule

/-! # Interchanging two ideal-power quotients

Source: Stacks Project, Tag 088A, the quotient by I^n + K^e
(blueprint: lem-weil-pbc-devissage-second-adic-system-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

private local instance quotientProjection_epi {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (F : X.Modules) : Epi (formalModuleQuotientπ I n F) := by
  dsimp [formalModuleQuotientπ]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private def quotientSwapMap {X : Scheme.{u}} (I K : X.IdealSheafData)
    (H : X.Modules) (e n : ℕ) :
    formalModuleQuotient I n (formalModuleQuotient K e H) ⟶
      formalModuleQuotient K e (formalModuleQuotient I n H) := by
  sorry
-/
-/
-/

@[reassoc (attr := simp)]
/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private theorem quotientSwapMap_projection {X : Scheme.{u}} (I K : X.IdealSheafData)
    (H : X.Modules) (e n : ℕ) :
    formalModuleQuotientπ K e H ≫
      formalModuleQuotientπ I n (formalModuleQuotient K e H) ≫
      quotientSwapMap I K H e n =
    formalModuleQuotientπ I n H ≫
      formalModuleQuotientπ K e (formalModuleQuotient I n H) := by
  simp [quotientSwapMap, formalModuleQuotientπ]
-/

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
private def quotientSwapIso {X : Scheme.{u}} (I K : X.IdealSheafData)
    (H : X.Modules) (e n : ℕ) :
    formalModuleQuotient I n (formalModuleQuotient K e H) ≅
      formalModuleQuotient K e (formalModuleQuotient I n H) where
  hom := quotientSwapMap I K H e n
  inv := quotientSwapMap K I H n e
  hom_inv_id := by
    apply (cancel_epi (formalModuleQuotientπ I n (formalModuleQuotient K e H))).1
    apply (cancel_epi (formalModuleQuotientπ K e H)).1
    simp only [quotientSwapMap_projection_assoc,
      quotientSwapMap_projection, Category.comp_id]
  inv_hom_id := by
    apply (cancel_epi (formalModuleQuotientπ K e (formalModuleQuotient I n H))).1
    apply (cancel_epi (formalModuleQuotientπ I n H)).1
    simp only [quotientSwapMap_projection_assoc,
      quotientSwapMap_projection, Category.comp_id]
-/

/-- The canonical quotient interchange, natural in both positive indices.
Source: Stacks Project, Tag 088A, the quotient by I^n + K^e
(blueprint: lem-weil-pbc-devissage-second-adic-system-comparison).

Proof: a map out of (H/K^e H)/I^n is precisely a map out of H killing both
K^e H and I^n H, by the two cokernel universal properties. Tensoring by an
ideal module preserves epimorphisms, so vanishing of its product can be checked
after the first quotient projection. The quotient in
the other order has the same property. Factor its composite projection through
the first quotient, and conversely. Both composites are identities: precompose
with the composite quotient projection, which is epi, and use the defining
factorization equations. These equations also give the displayed identity.
For either index transition, precomposing the naturality square with the
projection from H gives the same quotient projection on both paths. Epimorphism
cancellation proves the square, so the component isomorphisms assemble to θ.
-/
theorem grothendieckDevissage_secondAdicSystem_comparison
    {X : Scheme.{u}} (I K : X.IdealSheafData) (H : X.Modules) :
    ∃ (θ : formalCompletionSystem K H ⋙ formalCompletionFunctor I ≅
        (formalCompletionSystem I H ⋙ formalCompletionFunctor K).flip),
      ∀ e n : ℕ,
        formalModuleQuotientπ K (e + 1) H ≫
          formalModuleQuotientπ I (n + 1) (formalModuleQuotient K (e + 1) H) ≫
          (θ.hom.app (op e)).app (op n) =
        formalModuleQuotientπ I (n + 1) H ≫
          formalModuleQuotientπ K (e + 1) (formalModuleQuotient I (n + 1) H) := by
  sorry

end

end AlgebraicGeometry
