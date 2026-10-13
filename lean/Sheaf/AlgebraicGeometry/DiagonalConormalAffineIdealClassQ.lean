/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module
public import Sheaf.AlgebraicGeometry.DiagonalConormal
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.RingTheory.Kaehler.Basic
import Sheaf.AlgebraicGeometry.AffineConormalSectionsExistence
/-! # Affine diagonal cotangent comparison

Source: Stacks Project, Tags 08S2, 01KJ and 01R3.
(blueprint: stage3-diagonal-conormal-affine-ideal-class-q).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry
variable {X S : Scheme.{u}}
/-- Affine diagonal cotangent equivalence and unit formula, assuming tensor coordinates.
(blueprint: stage3-diagonal-conormal-affine-ideal-class-q)
Source: Stacks Project, Tags 08S2, 01KJ, 01R3.
Proof: Put A = Γ(X,U), R = Γ(S,V), B = A ⊗[R] A and J = ker μ.
The two projection formulas determine r on pure tensors, hence on B. They identify
the restricted diagonal U → W with Spec μ, a closed immersion since μ is onto.
Restriction to W preserves the actual module-sheaf kernel, and identifies it with
the closed immersion ideal module J. Inverse image of sheaves commutes with open
restriction, as does extension of scalars: both are the same inverse-image sheaf
followed by sheafification of the sectionwise tensor product. Their canonical units
restrict compatibly, since inverse-image unit followed by 1 ⊗ s is unchanged by
restriction and its sheafification unit is natural. Apply
Scheme.Modules.affine_conormal_sections_existence to this restricted closed
immersion. It gives an equivalence J/J² with the conormal sections, sending the
class of j to the restricted unit of any section s whose inclusion is r(j).
The B-action on J/J² factors through B/J, because every product of two
elements of J vanishes in J/J². Multiplication identifies B/J with A and sends
a ⊗ 1 to a. Thus the transported equivalence is A-linear for the first-factor action.
Mathlib's KaehlerDifferential R A is exactly J.Cotangent = J/J².
This yields e with the displayed formula. Any proof hδ gives the same restriction
map by proof irrelevance. The zero-ring chart obeys the same quotient calculation. -/
theorem diagonalConormal_affine_ideal_class_q (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    : letI : Algebra Γ(S, V.1) Γ(X, U.1) :=
        (f.appLE V.1 U.1 hUV).hom.toAlgebra
      let W := (pullback.fst f f) ⁻¹ᵁ U.1 ⊓ (pullback.snd f f) ⁻¹ᵁ U.1
      ∀ (r : (Γ(X, U.1) ⊗[Γ(S, V.1)] Γ(X, U.1)) ≃+* Γ(pullback f f, W)),
        (∀ a : Γ(X, U.1), r ((1 : Γ(X, U.1)) ⊗ₜ[Γ(S, V.1)] a) =
          (pullback.snd f f).appLE U.1 W inf_le_right a) →
        (∀ a : Γ(X, U.1), r (a ⊗ₜ[Γ(S, V.1)] (1 : Γ(X, U.1))) =
          (pullback.fst f f).appLE U.1 W inf_le_left a) →
        ∃ e : KaehlerDifferential Γ(S, V.1) Γ(X, U.1) ≃ₗ[Γ(X, U.1)]
            Γ(diagonalConormal f, U.1),
          ∀ (hδ : U.1 ≤ (pullback.diagonal f) ⁻¹ᵁ W)
            (j : KaehlerDifferential.ideal Γ(S, V.1) Γ(X, U.1))
            (s : Γ(kernel (SheafOfModules.unitToPushforwardObjUnit
              (pullback.diagonal f).toRingCatSheafHom), W)),
            (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
              (pullback.diagonal f).toRingCatSheafHom)).val.app (op W) s = r j →
            e (KaehlerDifferential.fromIdeal Γ(S, V.1) Γ(X, U.1) j) =
              (diagonalConormal f).presheaf.map (homOfLE hδ).op
                (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                  (pullback.diagonal f))).unit.app
                    (kernel (SheafOfModules.unitToPushforwardObjUnit
                      (pullback.diagonal f).toRingCatSheafHom))).val.app (op W) s) := by sorry
end AlgebraicGeometry
