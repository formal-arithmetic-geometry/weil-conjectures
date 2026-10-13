/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.RingTheory.Depth

/-!
# A finite flat model for depth-three punctured lifting

Source: Stacks Project, Tags 0BLS, 0BLL, 0BLH, 0BM6 and 09ZL.
(blueprint: lem-sbc-depth-three-punctured-finite-flat-model)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Construct a compatible finite flat model with etale principal quotient.

Source: Stacks Project, proof of Tag 0BLS through Tags 0BLL, 0BLH, 0BM6 and 09ZL;
depth and local cohomology are related by Tag 0AVY.
(blueprint: lem-sbc-depth-three-punctured-finite-flat-model)

Proof: Depth at least three makes the first and second maximal-ideal-supported
local cohomology vanish, hence they are annihilated by f. The quotient map is
injective on spectra and takes the closed point to the closed point, so its
inverse image of U is the punctured quotient spectrum. Pass to the maximal-ideal
adic completion. Flat base change preserves the cohomology vanishing and the
specified quotient extension. The completed ring is henselian along (f); lift
the base-changed quotient cover by 09ZL. Full faithfulness in 0BM6 identifies its
punctured restriction with the completed q. Apply finite algebra gluing 0BLH to
the completed finite algebra and q: this gives a finite A-algebra with both
specified restrictions. Flatness descends from its completed lift by faithful
flatness. Its quotient by f becomes the etale quotient lift after completion,
so etaleness of this quotient descends by faithful flatness too. Take the
spectrum of the glued algebra. The gluing isomorphism is over U, so it yields
the equality of morphisms asserted below. The zero algebra handles an empty
cover. No etaleness assertion about the whole model is needed in this step. -/
theorem exists_finite_flat_model_of_depth_three_of_quotient_extension
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} (q : Y ⟶ U.toScheme) [IsFinite q] [Etale q]
    (hquot :
      let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
      let V := i ⁻¹ᵁ U
      ∃ (F₀ : Scheme.{u}) (r₀ : F₀ ⟶ Spec (.of (A ⧸ Ideal.span {f}))),
        IsFinite r₀ ∧ Etale r₀ ∧
          ∃ e₀ : pullback q (i ∣_ U) ≅ (r₀ ⁻¹ᵁ V).toScheme,
            e₀.hom ≫ r₀ ∣_ V = pullback.snd q (i ∣_ U)) :
    ∃ (F : Scheme.{u}) (r : F ⟶ Spec (.of A)), IsFinite r ∧ Flat r ∧
      Etale (pullback.snd r
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))))) ∧
      ∃ e : Y ≅ (r ⁻¹ᵁ U).toScheme, e.hom ≫ r ∣_ U = q := by sorry

end AlgebraicGeometry.Scheme
