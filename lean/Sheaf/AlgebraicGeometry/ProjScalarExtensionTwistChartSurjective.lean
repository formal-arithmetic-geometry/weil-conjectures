/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistData
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Sheaf.RingTheory.HomogeneousLocalizationScalarExtension
import Sheaf.Algebra.Module.GradedLocalizationScalarExtension
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ProjTwistBasicOpenFractions

/-! The surjective half of the complete standard-chart scalar-extension comparison.
Source: Stacks Project, constructions.tex, Tags 01MY and 01N2.
(blueprint: new-sfb-proj-scalar-extension-twist-chart-surjective).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- The prescribed scalar-extension twist map is surjective on a complete standard chart.

Proof: The proof identifies chart sections with shifted homogeneous localized modules, applies
the affine tensor-section comparison and homogeneous localization scalar extension,
and uses the pointwise formula to identify that comparison with `η.app`. The remaining
affine chart identification is the source of this intermediate stage-3 statement.
Source: Stacks Project, constructions.tex, Tags 01MY and 01N2.
(blueprint: new-sfb-proj-scalar-extension-twist-chart-surjective). -/
theorem scalarExtension_twistMap_chart_surjective
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A)))
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ
      (HomogeneousIdeal.irrelevant 𝒜))
    (j : ℤ)
    (η : (tensorPullback (map ψ hψ)).obj (twist 𝒜 j) ⟶ twist ℬ j)
    (hη : ∀ (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 j, U))
      (x : map ψ hψ ⁻¹ᵁ U),
      ((η.app (map ψ hψ ⁻¹ᵁ U)
        (tensorPullbackSection (map ψ hψ) (twist 𝒜 j) U s)).1 x :
          Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
        Localization.localRingHom _ _ ψ.toRingHom rfl (s.1 ⟨_, x.2⟩).val)
    (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    Function.Surjective (η.app (basicOpen ℬ (ψ f))) := by
  sorry

end AlgebraicGeometry.Proj
