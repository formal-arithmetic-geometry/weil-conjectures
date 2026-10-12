/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ProperFinite.UnitSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-!
# Comparing a module with the twisted pushforward of its pullback

For `π : Y' ⟶ Y`, a section `s : 𝒪_{Y'} ⟶ L` and an `𝒪_Y`-module `𝒢`, the composite
`𝒢 ⟶ π_* π^* 𝒢 ⟶ π_* (π^* 𝒢 ⊗ L)` of the unit and of multiplication by `s` is an isomorphism
over every open `W` over which `π` is an isomorphism and `s` does not vanish.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {Y Y' : Scheme.{u}} (π : Y' ⟶ Y) {L : Y'.Modules} (s : 𝟙_ Y'.Modules ⟶ L)
  (𝒢 : Y.Modules)

/-- The composite `𝒢 ⟶ π_* π^* 𝒢 ⟶ π_* (π^* 𝒢 ⊗ L)` of the unit and of multiplication by `s`. -/
noncomputable def twistComparison : 𝒢 ⟶ (pushforward π).obj ((pullback π).obj 𝒢 ⊗ L) :=
  (pullbackPushforwardAdjunction π).unit.app 𝒢 ≫
    (pushforward π).map ((ρ_ _).inv ≫ _ ◁ s)

/-- `twistComparison π s 𝒢` is an isomorphism over every open `W` over which `π` is an
isomorphism and `s` does not vanish. -/
theorem isZero_restrict_kernel_cokernel_twistComparison [SheafOfModules.IsInvertible.{u, u, u} L]
    [𝒢.IsQuasicoherent] [QuasiCompact π] [QuasiSeparated π] (U : Y.Opens) [IsIso (π ∣_ U)]
    {W : Y.Opens} (hWU : W ≤ U) (hWs : π ⁻¹ᵁ W ≤ (Hom.zeroLocus s).support.compl) :
    IsZero ((kernel (twistComparison π s 𝒢)).restrict W.ι) ∧
      IsZero ((cokernel (twistComparison π s 𝒢)).restrict W.ι) :=
  sorry

end AlgebraicGeometry.Scheme.Modules
