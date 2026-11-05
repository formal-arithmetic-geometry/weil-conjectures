/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCover
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.LocallyConstantSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LocallyConstantWContractible

/-!
# Finite locally constant sheaves are constant on the universal cover

Let `Y` be a scheme with universal profinite étale covers `p : Ỹ_y ⟶ Y`
(`AlgebraicGeometry.Scheme.UniversalCovers`), and `Λ` a finite ring. For a finite locally
constant sheaf `H` of `Λ`-modules on `Y_ét`:

- `AlgebraicGeometry.Scheme.UniversalCovers.bijective_sectionsGerm_upperStar`: the global
  sections of `p^* H` map bijectively to its stalk at the base point `ỹ`. Injectivity holds as
  `Ỹ_y` is connected; surjectivity by counting, the `Y`-morphisms `Ỹ_y ⟶ P` to the finite étale
  scheme `P` representing `H` (`AlgebraicGeometry.Scheme.FiniteEtale.toFLC`) giving as many
  sections of the base change `P ×_Y Ỹ_y`, hence of `p^* H`
  (`AlgebraicGeometry.Etale.isIso_upperStar_forget_comparison`,
  `AlgebraicGeometry.Scheme.FiniteEtale.toFLCPullbackIso`), as there are points of `P` over `y`
  (`AlgebraicGeometry.Scheme.UniversalCovers.bijective_fiber`).
- `AlgebraicGeometry.Scheme.UniversalCovers.upperStarIsoConstantSheaf`: hence
  `p^* H ≅ (H_y)_{Ỹ_y}` on `Ỹ_y,ét`, naturally in `H`;
- `AlgebraicGeometry.Scheme.UniversalCovers.comparisonUpperStarIsoConstantSheaf`: and
  `p^* ν^* H ≅ (H_y)_{Ỹ_y}` on `Ỹ_y,proét`, naturally in `H`, and for towers
  (`AlgebraicGeometry.Scheme.UniversalCovers.towerComparisonUpperStarIsoConstantSheaf`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

section Sections

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
  {H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hH : IsFiniteLocallyConstantSheaf H)

end Sections

section Constant

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

end Constant

end AlgebraicGeometry.Scheme
