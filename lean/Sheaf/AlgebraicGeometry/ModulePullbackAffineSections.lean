/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.TensorPullbackTilde

/-!
# Sections of module pullback on affine opens

Source: Stacks Project, Schemes, Tags 01I9, 01IA, 01HV; Sheaves, Tags 00A0, 0097
(blueprint: lem-weil-pbc-module-pullback-affine-sections).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- The affine sections comparison is a bijective linear map, linear also for the action
of `B` on the second tensor factor, with its canonical pure-tensor formula and naturality.
The `B`-action on `G(V) ⊗[A] B` is written by swapping to `B ⊗[A] G(V)`, applying the usual
left-factor action, and swapping back; this avoids choosing a second tensor-module instance.
Source: Stacks Project, Schemes, Tags 01I9 (1), 01IA, 01HV (2); Sheaves, Tags 00A0, 0097
(blueprint: lem-weil-pbc-module-pullback-affine-sections).

Proof: (1) Use the canonical affine charts Spec A → Y and Spec B → X and their ring-map
square (lem-weil-pbc-affine-open-spec-points and
lem-weil-pbc-affine-opens-induced-ring-map-spec-square).
(2) Restrict G to Spec A and identify it with the tilde of G(V) by the affine tilde-Gamma
adjunction; its counit sends the section associated to s to s
(lem-weil-pbc-module-restriction-open-immersion-colimits,
lem-weil-pbc-spec-module-tilde-sections, lem-weil-pbc-affine-tilde-gamma-adjunction).
(3) Identify open-immersion pullback with restriction, compatibly with units
(lem-weil-pbc-open-immersion-module-pullback-restriction).
(4) Compare the two composite pullbacks through the chart square by uniqueness of adjoints;
the conjugate-isomorphism unit equation identifies their pulled-back sections
(def-weil-pbc-composite-adjunction, lem-weil-pbc-conjugate-iso-unit-equation).
(5) Apply the functorial tilde base-change isomorphism for A → B, taking the pullback of s
to the section associated to 1 ⊗ s (lem-weil-pbc-tilde-pullback-base-change).
(6) Take global sections and invert the resulting B-linear isomorphism, then swap tensor
factors. This gives c(s ⊗ b) = b • (f*s)|U and bijectivity.
(7) Naturality of the adjunction unit and compatibility of module morphisms with restriction
give the naturality equation on pure tensors. Additivity extends it to every tensor. -/
theorem exists_tensorPullback_affine_sections
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.affineOpens) (U : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    letI : Algebra Γ(Y, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
    letI : ∀ G : Y.Modules, Module Γ(Y, V.1) Γ((tensorPullback f).obj G, U.1) :=
      fun G ↦ Module.compHom _ (f.appLE V.1 U.1 hUV).hom
    ∃ c : ∀ (G : Y.Modules) (_ : G.IsQuasicoherent),
      (Γ(G, V.1) ⊗[Γ(Y, V.1)] Γ(X, U.1)) →ₗ[Γ(Y, V.1)]
        Γ((tensorPullback f).obj G, U.1),
      (∀ (G : Y.Modules) (hG : G.IsQuasicoherent), Function.Bijective (c G hG)) ∧
      (∀ (G : Y.Modules) (hG : G.IsQuasicoherent) (b : Γ(X, U.1))
          (t : Γ(G, V.1) ⊗[Γ(Y, V.1)] Γ(X, U.1)),
        c G hG ((TensorProduct.comm Γ(Y, V.1) Γ(G, V.1) Γ(X, U.1)).symm
          (b • TensorProduct.comm Γ(Y, V.1) Γ(G, V.1) Γ(X, U.1) t)) = b • c G hG t) ∧
      (∀ (G : Y.Modules) (hG : G.IsQuasicoherent) (s : Γ(G, V.1)) (b : Γ(X, U.1)),
        c G hG (s ⊗ₜ[Γ(Y, V.1)] b) =
          b • ((tensorPullback f).obj G).presheaf.map (homOfLE hUV).op
            (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G).val.app
              (op V.1) s)) ∧
      (∀ (G G' : Y.Modules) (hG : G.IsQuasicoherent) (hG' : G'.IsQuasicoherent)
          (a : G ⟶ G') (t : Γ(G, V.1) ⊗[Γ(Y, V.1)] Γ(X, U.1)),
        ((tensorPullback f).map a).app U.1 (c G hG t) =
          c G' hG' (TensorProduct.map (a.val.app (op V.1)).hom LinearMap.id t)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
