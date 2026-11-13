/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# Reflection of finite local constancy

## References

* Stacks Project, Tags 09AK and 099Y.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- Finite local constancy is reflected by the etale comparison pullback
(Stacks, Tag 099Y). -/
theorem isFiniteLocallyConstantSheaf_of_comparison_finite_models
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : ∃ (ι : Type (u + 1)) (W : ι → Scheme.{u}) (g : ∀ i, W i ⟶ X),
      Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty (((g i)^*[ModuleCat.{u + 1} Λ]).obj
            ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj G) ≅
              (constantSheaf (Scheme.ProEt.topology (W i)) (ModuleCat.{u + 1} Λ)).obj M)) :
    Scheme.IsFiniteLocallyConstantSheaf G := by
  have hLC : IsLocallyConstantProEtaleFixedModuleSheaf X Λ
      ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj G) := by
    obtain ⟨I, U, f, hf, h⟩ := finiteModels_over Λ _ hG
    exact ⟨I, U, f, hf, fun i ↦ by
      obtain ⟨M, _, he⟩ := h i
      exact ⟨M, he⟩⟩
  have hL : IsLisseProEtaleFixedModuleSheaf X Λ
      ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj G) :=
    ⟨hLC,
      finite_geometricStalk_of_finite_models Λ _ hG⟩
  obtain ⟨H, hH, ⟨e⟩⟩ := (proEtale_lisse_origin X Λ).2 _ hL
  have := hH
  exact IsFiniteLocallyConstantSheaf.of_iso
    ((ν^*(X)[ModuleCat.{u + 1} Λ]).preimageIso e)

end AlgebraicGeometry.ProEtale
