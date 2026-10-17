/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.CompletedBaseChange.Frobenius

/-!
# Frobenius data from equivalences

The exchange map of a square of adjunctions whose horizontal functors are equivalences is an
isomorphism (`CategoryTheory.isIso_mateEquiv_of_isEquivalence`): its iterated mate along the
adjoint equivalences is the conjugate of the original isomorphism. Consequently a Frobenius datum
on a base change square (`CategoryTheory.BaseChangeSquare.FrobeniusDatum`) whose Frobenius
pullbacks `Φ_Z = L Fr_Z^*` are equivalences (as they are for automorphisms `Fr_Z`) needs no
invertibility hypothesis on the exchange maps `β_f`, `β_{f'}`
(`CategoryTheory.BaseChangeSquare.FrobeniusDatum.ofIsEquivalence`,
`def-weil-pbc-frobenius-tower-datum`: "since every `Fr_Z` is an automorphism, every `Φ_Z` is an
exact equivalence").
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]

/-- **The exchange map of a square with equivalences as horizontal functors is invertible**:
for adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂` and an isomorphism `α : G ⋙ L₂ ≅ L₁ ⋙ H` with `G` and `H`
equivalences, the mate `R₁ ⋙ G ⟶ H ⋙ R₂` of `α` is an isomorphism. -/
lemma isIso_mateEquiv_of_isEquivalence {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A}
    {L₂ : C ⥤ D} {R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H)
    [IsIso α.natTrans] [G.IsEquivalence] [H.IsEquivalence] :
    IsIso (mateEquiv adj₁ adj₂ α).natTrans := by
  let adj₃ := G.asEquivalence.toAdjunction
  let adj₄ := H.asEquivalence.toAdjunction
  set β := mateEquiv adj₁ adj₂ α
  have h : IsIso (mateEquiv adj₄ adj₃ β).natTrans := by
    rw [iterated_mateEquiv_conjugateEquiv adj₁ adj₂ adj₃ adj₄ α]
    infer_instance
  have key : ∀ d : D, IsIso (β.natTrans.app (H.inv.obj d)) := fun d ↦ by
    have he : (mateEquiv adj₄ adj₃ β).natTrans.app d = adj₃.unit.app (R₁.obj (H.inv.obj d)) ≫
        G.inv.map (β.natTrans.app (H.inv.obj d) ≫ R₂.map (adj₄.counit.app d)) := by
      simp [mateEquiv_apply]
    have e : IsIso ((mateEquiv adj₄ adj₃ β).natTrans.app d) := inferInstance
    rw [he] at e
    have : IsIso (adj₃.unit.app (R₁.obj (H.inv.obj d))) := by dsimp [adj₃]; infer_instance
    have : IsIso (G.inv.map (β.natTrans.app (H.inv.obj d) ≫ R₂.map (adj₄.counit.app d))) :=
      IsIso.of_isIso_comp_left (adj₃.unit.app _) _
    have : IsIso (β.natTrans.app (H.inv.obj d) ≫ R₂.map (adj₄.counit.app d)) :=
      isIso_of_reflects_iso _ G.inv
    have : IsIso (adj₄.counit.app d) := by dsimp [adj₄]; infer_instance
    exact IsIso.of_isIso_comp_right _ (R₂.map (adj₄.counit.app d))
  rw [NatTrans.isIso_iff_isIso_app]
  intro b
  have hη : IsIso (adj₄.unit.app b) := by dsimp [adj₄]; infer_instance
  have w := β.natTrans.naturality (adj₄.unit.app b)
  dsimp at w
  have : β.natTrans.app b = G.map (R₁.map (adj₄.unit.app b)) ≫
      β.natTrans.app (H.inv.obj (H.obj b)) ≫ inv (R₂.map (H.map (adj₄.unit.app b))) := by
    rw [reassoc_of% w, IsIso.hom_inv_id, Category.comp_id]
  rw [this]
  have := key (H.obj b)
  infer_instance
namespace BaseChangeSquare.FrobeniusDatum

variable {𝒯 : Type u₁} {𝒰 : Type u₂} {𝒯' : Type u₃} {𝒰' : Type u₄}
  [Category.{v₁} 𝒯] [Category.{v₂} 𝒰] [Category.{v₃} 𝒯'] [Category.{v₄} 𝒰']
  {𝔗 : BaseChangeSquare 𝒯 𝒰 𝒯' 𝒰'}

/-- A Frobenius datum (Blueprint `def-weil-pbc-frobenius-tower-datum`) whose Frobenius pullbacks
are equivalences: the invertibility of the exchange maps `β_f`, `β_{f'}` of the proper Frobenius
faces is then automatic (`CategoryTheory.isIso_mateEquiv_of_isEquivalence`). -/
noncomputable def ofIsEquivalence (ΦX : 𝒯 ⥤ 𝒯) (ΦY : 𝒰 ⥤ 𝒰) (ΦX' : 𝒯' ⥤ 𝒯') (ΦY' : 𝒰' ⥤ 𝒰')
    [ΦX.IsEquivalence] [ΦY.IsEquivalence] [ΦX'.IsEquivalence] [ΦY'.IsEquivalence]
    (κF : 𝔗.upperF ⋙ ΦX ≅ ΦY ⋙ 𝔗.upperF) (κF' : 𝔗.upperF' ⋙ ΦX' ≅ ΦY' ⋙ 𝔗.upperF')
    (κG : 𝔗.upperG ⋙ ΦY' ≅ ΦY ⋙ 𝔗.upperG) (κG' : 𝔗.upperG' ⋙ ΦX' ≅ ΦX ⋙ 𝔗.upperG')
    (cube : ((TwoSquare.mk _ _ _ _ κF.inv ≫ₕ 𝔗.isoSquare).whiskerTop κG.hom) =
      ((𝔗.isoSquare ≫ₕ TwoSquare.mk _ _ _ _ κF'.inv).whiskerBottom κG'.hom)) :
    FrobeniusDatum 𝔗 where
  ΦX := ΦX
  ΦY := ΦY
  ΦX' := ΦX'
  ΦY' := ΦY'
  κF := κF
  κF' := κF'
  κG := κG
  κG' := κG'
  isIso_βF := isIso_mateEquiv_of_isEquivalence _ _ _
  isIso_βF' := isIso_mateEquiv_of_isEquivalence _ _ _
  cube := cube

end BaseChangeSquare.FrobeniusDatum

end CategoryTheory
