/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitting
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplittingPullback
import WeilConjectures.AlgebraicGeometry.FiniteSectionCoproductLocalPermutation

/-!
# Local sheet correspondence for two finite clopen splittings

## References

* Stacks Project, Tag 03SH
* SGA 4, Exposé IX, 5.1
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sections_isColimit {X Y : Scheme.{u}} {f : Y ⟶ X} {T : X.Etale}
    (D : FiniteEtaleTraceSplitting f T) :
    IsColimit (Cofan.mk (pullback T.hom f) (fun j ↦ D.t j ≫ D.i j)) := by
  refine Cofan.IsColimit.mk _ (fun c ↦ D.colimit.desc
    (Cofan.mk c.pt (fun j ↦ D.i j ≫ pullback.fst T.hom f ≫ c.inj j))) ?_ ?_
  · intro c j
    change (D.t j ≫ D.i j) ≫ _ = _
    have hh : D.i j ≫ D.colimit.desc
        (Cofan.mk c.pt (fun j ↦ D.i j ≫ pullback.fst T.hom f ≫ c.inj j)) =
        D.i j ≫ pullback.fst T.hom f ≫ c.inj j := D.colimit.fac _ ⟨j⟩
    rw [Category.assoc, hh]
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ c.inj j) (D.inv₁ j)
  · intro c m hm
    apply D.colimit.hom_ext
    intro ⟨j⟩
    change D.i j ≫ m = _
    rw [D.colimit.fac _ ⟨j⟩]
    calc
      _ = (D.i j ≫ pullback.fst T.hom f ≫ D.t j) ≫ D.i j ≫ m := by
        rw [D.inv₂, Category.id_comp]
      _ = D.i j ≫ pullback.fst T.hom f ≫ c.inj j := by
        simpa [Category.assoc] using congrArg
          (fun k ↦ D.i j ≫ pullback.fst T.hom f ≫ k) (hm j)

set_option backward.isDefEq.respectTransparency false in
/-- Two finite splittings of the same pullback admit a local correspondence of sheets.
(Stacks, Section 03SH, after Definition 03SE; SGA 4, Exposé IX, 5.1.) -/
theorem finiteEtaleTrace_split_reindexing {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : Etale f) :
    let B := MorphismProperty.Over.pullback @Etale ⊤ f ⋙ MorphismProperty.Over.map ⊤ hf
    ∀ (W T₁ T₂ Z : X.Etale) (h₁ : T₁ ⟶ W) (h₂ : T₂ ⟶ W)
      (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂), g₁ ≫ h₁ = g₂ ≫ h₂ →
      ∀ (D₁ : FiniteEtaleTraceSplitting f T₁) (D₂ : FiniteEtaleTraceSplitting f T₂),
      ∃ R : Presieve Z, Sieve.generate R ∈ X.smallEtaleTopology Z ∧
        ∀ (Q : X.Etale) (k : Q ⟶ Z), R k → ∃ e : D₁.J ≃ D₂.J,
          ∀ j, k ≫ g₁ ≫ D₁.sectionMap hf j ≫ B.map h₁ =
            k ≫ g₂ ≫ D₂.sectionMap hf (e j) ≫ B.map h₂ := by
  classical
  dsimp only
  intro W T₁ T₂ Z h₁ h₂ g₁ g₂ he D₁ D₂
  let B := MorphismProperty.Over.pullback @Etale ⊤ f ⋙ MorphismProperty.Over.map ⊤ hf
  obtain ⟨E₁, e₁, hE₁⟩ := finiteEtaleTrace_splitting_pullback f hf T₁ Z g₁ D₁
  obtain ⟨E₂, e₂, hE₂⟩ := finiteEtaleTrace_splitting_pullback f hf T₂ Z g₂ D₂
  let := E₁.finiteIndex
  let := E₂.finiteIndex
  have hlocal (z : Z.left) : ∃ (Q : X.Etale) (k : Q ⟶ Z),
      z ∈ Set.range k.left ∧ ∃ e : E₁.J ≃ E₂.J,
        ∀ j, k ≫ E₁.sectionMap hf j = k ≫ E₂.sectionMap hf (e j) := by
    obtain ⟨U, hz, e, hu⟩ := finiteSectionCoproduct_local_permutation
      Z.left (pullback Z.hom f) (pullback.fst Z.hom f) E₁.J E₂.J
      (fun j ↦ E₁.t j ≫ E₁.i j) (fun j ↦ E₂.t j ≫ E₂.i j)
      (sections_isColimit E₁) (sections_isColimit E₂) E₁.inv₁ E₂.inv₁ z
    let Q : X.Etale := MorphismProperty.Over.mk ⊤ (U.ι ≫ Z.hom) inferInstance
    let k : Q ⟶ Z := MorphismProperty.Over.homMk U.ι rfl
    refine ⟨Q, k, ?_, e, ?_⟩
    · exact ⟨⟨z, hz⟩, rfl⟩
    · intro j
      apply MorphismProperty.Over.Hom.ext
      exact hu j
  choose Q k hk e hsections using hlocal
  let R : Presieve Z := Presieve.ofArrows Q k
  refine ⟨R, ?_, ?_⟩
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff k).mpr
    exact Set.eq_univ_of_forall fun z ↦ Set.mem_iUnion.mpr ⟨z, hk z⟩
  · intro V l hl
    obtain ⟨z⟩ := hl
    refine ⟨e₁.trans ((e z).trans e₂.symm), ?_⟩
    intro j
    have hmatch := hsections z (e₁ j)
    have hright := hE₂ (e₂.symm (e z (e₁ j)))
    simp only [Equiv.apply_symm_apply] at hright
    calc
      _ = k z ≫ E₁.sectionMap hf (e₁ j) ≫ B.map (g₁ ≫ h₁) := by
        simpa [Category.assoc, B] using congrArg
          (fun a ↦ k z ≫ a ≫ B.map h₁) (hE₁ j)
      _ = k z ≫ E₂.sectionMap hf (e z (e₁ j)) ≫ B.map (g₂ ≫ h₂) := by
        rw [he]
        simpa [Category.assoc] using congrArg (fun a ↦ a ≫ B.map (g₂ ≫ h₂)) hmatch
      _ = _ := by
        rw [B.map_comp]
        simp only [Equiv.trans_apply]
        simpa [Category.assoc, B] using congrArg
          (fun a ↦ k z ≫ a ≫ B.map h₂) hright.symm

end AlgebraicGeometry.Etale
