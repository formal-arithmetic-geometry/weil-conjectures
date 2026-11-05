/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverMilnor

/-!
# The Milnor sequence on the universal cover, for abelian sheaves

The abelian version of `WeilConjectures.SixFunctors.ProEtale.Comparison.UniversalCoverMilnor`, for
derived limits of towers of complexes of abelian pro-étale sheaves (such as
`Rg_* 𝒪_{E,T} ≅ R lim_n ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)`,
`isHomotopyLimit_comparisonUpperStar_rightDerivedLowerStar_constantSheafTower`)
whose cohomology towers are, after pullback to the universal cover `p : Ỹ_y ⟶ Y`, the abelian
towers underlying `p^* ν^* Hₙ` for towers `H` of étale sheaves of `Λ`-modules with finite locally
constant underlying sheaves of sets (`AlgebraicGeometry.Scheme.IsSetFLC`):

- `AlgebraicGeometry.Scheme.UniversalCovers.isLimitHomologyUpperStarAbOfIsSetFLC`:
  `Hⁱ(p^* R lim F) = lim_n Hⁱ(p^* Fₙ)`;
- `AlgebraicGeometry.Scheme.UniversalCovers.nonempty_iso_homologyUpperStar_continuousMapAddSheaf`:
  `Hⁱ(p^* R lim F) ≅ C(-, lim_n (Hₙ)_y)`, the integral identification on the universal cover.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

section Forget

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- Taking underlying abelian sheaves of pro-étale sheaves of `Λ`-modules is left exact. -/
instance ProEt.preservesFiniteLimits_sheafCompose_forget₂ :
    PreservesFiniteLimits (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  have : PreservesFiniteLimits (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

/-- Taking underlying abelian sheaves of pro-étale sheaves of `Λ`-modules preserves
epimorphisms, which are the locally surjective morphisms. -/
instance ProEt.preservesEpimorphisms_sheafCompose_forget₂ :
    (sheafCompose (ProEt.topology X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).PreservesEpimorphisms :=
  ⟨fun f _ ↦ by
    have hf : Sheaf.IsLocallySurjective f := (Sheaf.isLocallySurjective_iff_epi' (φ := f)).2
      inferInstance
    have : Sheaf.IsLocallySurjective ((sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map f) :=
      ⟨fun s ↦ hf.imageSieve_mem s⟩
    exact Sheaf.epi_of_isLocallySurjective _⟩

end Forget

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] (U : Scheme.UniversalCovers Y Ω)
  (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {Λ : Type (u + 1)} [Ring Λ]

end AlgebraicGeometry.Scheme
