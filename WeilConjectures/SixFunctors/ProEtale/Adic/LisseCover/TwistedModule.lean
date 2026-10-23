/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-!
# The étale sheaf of modules of a linear descent cocycle

Let `f : V ⟶ Y` be weakly étale, `M` a `Λ`-module and `c` a descent cocycle on the constant sheaf
`M_V` acting by `Λ`-linear automorphisms. The twisted sections of `c`
(`AlgebraicGeometry.IsTwistedSection`) over an étale `Y`-scheme form a `Λ`-submodule of the
functions to `M` (`AlgebraicGeometry.twistedSubmodule`), and these submodules form a sheaf of
`Λ`-modules on the small étale site of `Y` (`AlgebraicGeometry.twistedModuleSheaf`), whose
underlying sheaf of sets is `AlgebraicGeometry.twistedSectionsPresheaf`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {Y V : Scheme.{u}} (f : V ⟶ Y) {Λ : Type (u + 1)} [CommRing Λ] {M : Type (u + 1)}
  [AddCommGroup M] [Module Λ M] (c : ↥(pullback f f) → M ≃ₗ[Λ] M)

/-- The twisted sections of a linear cocycle over `π : T ⟶ Y` form a `Λ`-submodule of the
functions `V ×_Y T → M`. -/
def twistedSubmodule {T : Scheme.{u}} (π : T ⟶ Y) : Submodule Λ (↥(pullback f π) → M) where
  carrier := {σ | IsTwistedSection f (fun z ↦ c z) π σ}
  add_mem' {σ τ} hσ hτ := ⟨hσ.1.add hτ.1, fun w ↦ by
    simp only [Pi.add_apply, hσ.2 w, hτ.2 w, map_add]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun w ↦ by simp⟩
  smul_mem' a σ hσ := ⟨hσ.1.comp (a • ·), fun w ↦ by
    simp only [Pi.smul_apply, hσ.2 w, map_smul]⟩

/-- The presheaf of `Λ`-modules of twisted sections of a linear cocycle on the small étale site
of `Y`. -/
noncomputable def twistedModulePresheaf : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ where
  obj U := ModuleCat.of Λ (twistedSubmodule f c U.unop.hom)
  map {U U'} g := ModuleCat.ofHom
    { toFun σ := ⟨σ.1 ∘ (pullbackMapRight f g.unop.left (MorphismProperty.Over.w g.unop)).base,
        σ.2.comp g.unop.left (MorphismProperty.Over.w g.unop)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id U := by
    ext σ : 2
    refine Subtype.ext ?_
    change σ.1 ∘ (pullbackMapRight f (𝟙 U.unop.left) _).base = σ.1
    rw [pullbackMapRight_id]
    rfl
  map_comp {U U' U''} g g' := by
    ext σ : 2
    refine Subtype.ext ?_
    change σ.1 ∘ (pullbackMapRight f (g'.unop.left ≫ g.unop.left) _).base =
      (σ.1 ∘ (pullbackMapRight f g.unop.left _).base) ∘ (pullbackMapRight f g'.unop.left _).base
    rw [pullbackMapRight_comp g.unop.left (MorphismProperty.Over.w g.unop) g'.unop.left
      (MorphismProperty.Over.w g'.unop)]
    rfl

/-- The underlying presheaf of sets of `AlgebraicGeometry.twistedModulePresheaf` is the presheaf
of twisted sections `AlgebraicGeometry.twistedSectionsPresheaf`. -/
noncomputable def twistedModulePresheafCompForgetIso :
    twistedModulePresheaf f c ⋙ forget (ModuleCat.{u + 1} Λ) ≅
      twistedSectionsPresheaf f (fun z ↦ c z) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- **The sheaf of `Λ`-modules of twisted sections of a linear cocycle.** -/
noncomputable def twistedModuleSheaf : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj := twistedModulePresheaf f c
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget (ModuleCat.{u + 1} Λ)),
      Presheaf.isSheaf_of_iso_iff (twistedModulePresheafCompForgetIso f c)]
    exact isSheaf_twistedSectionsPresheaf f _

section PullbackComparison

variable {f c}

/-- The pullback of a linear cocycle along `π : T ⟶ Y`, a cocycle for the cover
`V ×_Y T ⟶ T`. -/
noncomputable def pullbackCocycle {T : Scheme.{u}} (π : T ⟶ Y) :
    ↥(pullback (pullback.snd f π) (pullback.snd f π)) → M ≃ₗ[Λ] M :=
  fun w ↦ c ((twistedPairMap f π).base w)

/-- **Pullback of twisted sheaves.** For any `π : T ⟶ Y`, the pullback of the sheaf of twisted
sections of `c` is the sheaf of twisted sections of the pulled back cocycle. -/
noncomputable def upperStarTwistedModuleSheafIso [WeaklyEtale f] [Surjective f] [QuasiCompact f]
    (hc : IsDescentCocycle f (fun z ↦ c z)) {T : Scheme.{u}} (π : T ⟶ Y) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) π).obj (twistedModuleSheaf f c) ≅
      twistedModuleSheaf (pullback.snd f π) (pullbackCocycle π) :=
  sorry

/-- **Global sections of pulled back twisted sheaves.** If the pullback of global sections
along `q : Q ⟶ P` is bijective for the pullback of the sheaf of twisted sections of `c` to
`p : P ⟶ Y`, then restriction of twisted sections from `P` to `Q` is bijective. -/
theorem bijective_twistedRestrict_of_isIso_globalSectionsUpperStarMap [WeaklyEtale f]
    [Surjective f] [QuasiCompact f] (hc : IsDescentCocycle f (fun z ↦ c z)) {P Q : Scheme.{u}}
    (p : P ⟶ Y) (q : Q ⟶ P)
    (h : IsIso (Etale.globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj (twistedModuleSheaf f c)))) :
    Function.Bijective (fun σ : twistedSubmodule f c p ↦
      (⟨σ.1 ∘ (pullbackMapRight f q rfl).base, σ.2.comp q rfl⟩ :
        twistedSubmodule f c (q ≫ p))) :=
  sorry

end PullbackComparison

end AlgebraicGeometry
