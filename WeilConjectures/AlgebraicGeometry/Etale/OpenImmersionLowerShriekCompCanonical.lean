/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry
open Etale

/-- The extension comparison is the generic left-adjoint comparison induced by `upperStarComp`.
This identification is obtained by unfolding `openImmersionLowerShriekComp` and the mate
construction; it is recorded separately so dependent transports for identity and associativity
can be handled before applying the generic coherence lemmas. The proof unfolds both mate
constructions,
uses the defining conjugate equivalence and its unit equation, and applies proof irrelevance to
all scheme-morphism equality transports.
(blueprint: lem-cbc-extension-zero-composition-canonical-comparison) -/
theorem Etale.openImmersionLowerShriekComp_canonical
    (Λ : Type (u + 1)) [CommRing Λ] :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) (𝟙 U) j).inv.app F ≫
        eqToHom (by simp only [Category.id_comp]) =
      (Adjunction.leftAdjointCompIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 U))
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
        (upperStarComp (ModuleCat.{u + 1} Λ) (𝟙 U) j j
          (Category.id_comp j).symm).symm).hom.app F) ∧
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) j (𝟙 X)).inv.app F ≫
        eqToHom (by simp only [Category.comp_id]) =
      (Adjunction.leftAdjointCompIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
        (upperStarComp (ModuleCat.{u + 1} Λ) j (𝟙 X) j
          (Category.comp_id j).symm).symm).hom.app F) ∧
    (∀ {U V W : Scheme.{u}} (j₁ : U ⟶ V) (j₂ : V ⟶ W)
      [IsOpenImmersion j₁] [IsOpenImmersion j₂]
      (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) j₁ j₂).inv.app F =
      (Adjunction.leftAdjointCompIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₁)
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₂)
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (j₁ ≫ j₂))
        (upperStarComp (ModuleCat.{u + 1} Λ) j₁ j₂).symm).hom.app F) ∧
    (∀ {U V W X : Scheme.{u}} (j₁ : U ⟶ V) (j₂ : V ⟶ W) (j₃ : W ⟶ X)
      [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₃]
      (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) (j₁ ≫ j₂) j₃).inv.app F ≫
        eqToHom (by simp only [Category.assoc]) =
      (Adjunction.leftAdjointCompIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (j₁ ≫ j₂))
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₃)
        (openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) (j₁ ≫ j₂ ≫ j₃))
        (upperStarComp (ModuleCat.{u + 1} Λ) (j₁ ≫ j₂) j₃
          (j₁ ≫ j₂ ≫ j₃) (by simp [Category.assoc])).symm).hom.app F) := by
  -- Uniqueness after right-adjoint transport has the same unit/counit formula as mates.
  have comparison {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
      {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
      (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : R₂ ≅ R₁) (M : C) :
      (adj₁.leftAdjointUniq (adj₂.ofNatIsoRight e)).inv.app M =
        ((conjugateIsoEquiv adj₁ adj₂).symm e.symm).hom.app M := by
    simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]
  -- Substitute the chosen composite before comparing the dependent functors.
  have transported {U V W : Scheme.{u}} (j₁ : U ⟶ V) (j₂ : V ⟶ W)
      [IsOpenImmersion j₁] [IsOpenImmersion j₂]
      (j₁₂ : U ⟶ W) [IsOpenImmersion j₁₂] (h : j₁₂ = j₁ ≫ j₂)
      (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) j₁ j₂).inv.app F ≫
          eqToHom (by subst j₁₂; rfl) =
        (Adjunction.leftAdjointCompIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₁)
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₂)
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₁₂)
          (upperStarComp (ModuleCat.{u + 1} Λ) j₁ j₂ j₁₂ h).symm).hom.app F := by
    subst j₁₂
    simpa only [eqToHom_refl, Category.comp_id, openImmersionLowerShriekComp,
      Adjunction.leftAdjointCompIso] using
      comparison
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (j₁ ≫ j₂))
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₁).comp
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₂))
        (upperStarComp (ModuleCat.{u + 1} Λ) j₁ j₂).symm F
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro U X j _ F
    exact transported (𝟙 U) j j (Category.id_comp j).symm F
  · intro U X j _ F
    exact transported j (𝟙 X) j (Category.comp_id j).symm F
  · intro U V W j₁ j₂ _ _ F
    simpa only [eqToHom_refl, Category.comp_id] using
      transported j₁ j₂ (j₁ ≫ j₂) rfl F
  · intro U V W X j₁ j₂ j₃ _ _ _ F
    exact transported (j₁ ≫ j₂) j₃ (j₁ ≫ j₂ ≫ j₃) (by simp only [Category.assoc]) F

end AlgebraicGeometry
