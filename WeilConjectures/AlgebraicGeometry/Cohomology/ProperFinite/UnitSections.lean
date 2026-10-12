/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.AlgebraicGeometry.Modules.VanishingOnOpen

/-!
# The unit of `f^* ⊣ f_*` on sections over affine opens

For a quasi-coherent `ℱ` and affine opens `V` and `f ⁻¹ᵁ V`, the unit `ℱ ⟶ f_* f^* ℱ` on
sections over `V` is `m ↦ 1 ⊗ m : Γ(ℱ, V) ⟶ Γ(X, f ⁻¹ᵁ V) ⊗ Γ(ℱ, V)`. Hence it is bijective if
`f.app V` is, and for a closed immersion it is surjective with kernel `I • Γ(ℱ, V)`.
We also record criteria for a morphism to be an isomorphism over an open.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- If `V` and `f ⁻¹ᵁ V` are affine and `f.app V` is bijective, the unit of `f^* ⊣ f_*` is
bijective on sections over `V`. -/
theorem bijective_unit_app_of_bijective (f : X ⟶ Y) (ℱ : Y.Modules) [ℱ.IsQuasicoherent]
    {V : Y.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (hf : Function.Bijective (f.app V)) :
    Function.Bijective (((pullbackPushforwardAdjunction f).unit.app ℱ).app V) :=
  sorry

/-- For a closed immersion `i`, the unit of `i^* ⊣ i_*` is surjective on sections over affine
opens. -/
theorem surjective_unit_app_of_isClosedImmersion (i : X ⟶ Y) [IsClosedImmersion i]
    (ℱ : Y.Modules) [ℱ.IsQuasicoherent] {V : Y.Opens} (hV : IsAffineOpen V) :
    Function.Surjective (((pullbackPushforwardAdjunction i).unit.app ℱ).app V) :=
  sorry

/-- For a closed immersion `i` and quasi-coherent `ℱ`, the unit `ℱ ⟶ i_* i^* ℱ` is an
epimorphism. -/
instance epi_unit_app_of_isClosedImmersion (i : X ⟶ Y) [IsClosedImmersion i] (ℱ : Y.Modules)
    [ℱ.IsQuasicoherent] : Epi ((pullbackPushforwardAdjunction i).unit.app ℱ) :=
  sorry

/-- For a closed immersion `i` and quasi-coherent `ℱ`, the sections over an affine open `V` of
the kernel of the unit `ℱ ⟶ i_* i^* ℱ` are `I • Γ(ℱ, V)`, for `I` the kernel of `i.app V`. -/
theorem range_kernelι_unit_app (i : X ⟶ Y) [IsClosedImmersion i] (ℱ : Y.Modules)
    [ℱ.IsQuasicoherent] {V : Y.Opens} (hV : IsAffineOpen V) :
    Set.range ((kernel.ι ((pullbackPushforwardAdjunction i).unit.app ℱ)).app V) =
      ((RingHom.ker (i.app V).hom • ⊤ : Submodule Γ(Y, V) Γ(ℱ, V)) : Set Γ(ℱ, V)) :=
  sorry

/-- A morphism which is an isomorphism over `W` is bijective on sections over opens in `W`. -/
theorem bijective_app_of_isIso_restrictFunctor_map {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens)
    [IsIso ((restrictFunctor W.ι).map φ)] {V : X.Opens} (hV : V ≤ W) :
    Function.Bijective (φ.app V) :=
  sorry

/-- A morphism of quasi-coherent modules which is bijective on sections over the affine opens
contained in `W` has kernel and cokernel vanishing on `W`. -/
theorem isZero_restrict_kernel_and_cokernel {M N : X.Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (φ : M ⟶ N) (W : X.Opens)
    (h : ∀ V : X.Opens, IsAffineOpen V → V ≤ W → Function.Bijective (φ.app V)) :
    IsZero ((kernel φ).restrict W.ι) ∧ IsZero ((cokernel φ).restrict W.ι) :=
  sorry

end AlgebraicGeometry.Scheme.Modules
