/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningExists
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-!
# Conormal sheaf of a formally unramified morphism

Source: Stacks Project, More on Morphisms, Definition 04F4 (2), and Morphisms,
Definition 01R2 (blueprint: def-weil-pbc-conormal-sheaf-formally-unramified).
-/

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- The conormal sheaf for the chosen universal first order thickening of `h`.
Its ideal is `i.ker`, and its square is zero by `H.1.2`; hence pulling back the ideal
is the same conormal module as pulling back its quotient by its square.
Source: Stacks Project, Definition 04F4 (2) and Definition 01R2
(blueprint: def-weil-pbc-conormal-sheaf-formally-unramified). -/
noncomputable def formallyUnramifiedConormal {Z X Z' : Scheme.{u}}
    (h : Z ⟶ X) [FormallyUnramified h] (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (_H : IsUniversalFirstOrderThickening h i h') : Z.Modules :=
  (Scheme.Modules.tensorPullback i).obj i.ker.toModules

/-- Existence of a choice and independence of the conormal sheaf under the unique
compatible comparison of universal thickenings. The module isomorphism is uniquely
determined by carrying the pullback of each ideal section to the pullback of its
image under the scheme comparison. The restrictions to `W` put both sections on
the same open of `Z`.
Source: Stacks Project, Tags 04F2, 04F3, 04F4 (2) and 01R2
(blueprint: def-weil-pbc-conormal-sheaf-formally-unramified).
Proof: (1) Use `FormallyUnramified.exists_universalFirstOrderThickening` to obtain
one universal thickening and the unique compatible isomorphism between any two.
(2) Its ideal is the kernel ideal sheaf (def-sbc-closed-immersion-ideal-sheaf);
first order means its square is zero, so the quotient by the square is the ideal.
(3) Apply the tensor module pullback (def-pc-module-pullback) to that ideal.
(4) The compatible scheme isomorphism identifies the two kernel ideal sheaves;
functoriality of tensor pullback identifies their pullbacks on the common `Z`.
The scheme comparison is unique by the universal property, so this identification
is canonical and independent of the chosen thickening. Pullbacks of ideal sections
locally generate the conormal module, so the displayed section equation determines
the module isomorphism uniquely. -/
theorem formallyUnramifiedConormal_independent {Z X : Scheme.{u}}
    (h : Z ⟶ X) [FormallyUnramified h] :
    (∃ (Z' : Scheme.{u}) (i : Z ⟶ Z') (h' : Z' ⟶ X),
      IsUniversalFirstOrderThickening h i h') ∧
    ∀ (Z₁ Z₂ : Scheme.{u}) (i₁ : Z ⟶ Z₁) (h₁ : Z₁ ⟶ X)
      (i₂ : Z ⟶ Z₂) (h₂ : Z₂ ⟶ X)
      (H₁ : IsUniversalFirstOrderThickening h i₁ h₁)
      (H₂ : IsUniversalFirstOrderThickening h i₂ h₂),
      ((∃! φ : Z₁ ⟶ Z₂, φ ≫ h₂ = h₁ ∧ i₁ ≫ φ = i₂) ∧
        ∀ φ : Z₁ ⟶ Z₂, φ ≫ h₂ = h₁ → i₁ ≫ φ = i₂ → IsIso φ) ∧
      ∀ (φ : Z₁ ⟶ Z₂), φ ≫ h₂ = h₁ → i₁ ≫ φ = i₂ →
        ∃! e : formallyUnramifiedConormal h i₂ h₂ H₂ ≅
            formallyUnramifiedConormal h i₁ h₁ H₁,
          ∀ (U : Z₂.Opens) (s₂ : Γ(i₂.ker.toModules, U))
            (s₁ : Γ(i₁.ker.toModules, φ ⁻¹ᵁ U)),
            i₁.ker.toModulesι.app (φ ⁻¹ᵁ U) s₁ =
              φ.app U (i₂.ker.toModulesι.app U s₂) →
            ∀ (W : Z.Opens) (a : W ≤ i₂ ⁻¹ᵁ U) (b : W ≤ i₁ ⁻¹ᵁ (φ ⁻¹ᵁ U)),
              e.hom.app W
                  ((formallyUnramifiedConormal h i₂ h₂ H₂).val.map (homOfLE a).op
                    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                      i₂)).unit.app i₂.ker.toModules).app U s₂)) =
                (formallyUnramifiedConormal h i₁ h₁ H₁).val.map (homOfLE b).op
                  (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                    i₁)).unit.app i₁.ker.toModules).app (φ ⁻¹ᵁ U) s₁) := by
  sorry

end AlgebraicGeometry
