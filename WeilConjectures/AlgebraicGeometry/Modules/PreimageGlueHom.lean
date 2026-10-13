/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PreimageGlue
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Gluing morphisms for modules defined on other schemes

Let `U a` be a family of opens of a scheme `S` and let `O a` be modules on schemes `W a`. For a
morphism `g : Z ⟶ S` together with morphisms `μ a : g⁻¹ U a ⟶ W a`, we consider *gluing
morphisms* `H a b` between the pullbacks of `O a` and `O b` to `g⁻¹ (U a ⊓ U b)`
(`AlgebraicGeometry.Scheme.Modules.GlueHom`), without the cocycle conditions. They can be pulled
back along any morphism `h : Z' ⟶ Z` over `S` (`GlueHom.pull`), and the identity and cocycle
conditions (`GlueHom.SelfCond`, `GlueHom.CocycleCond`) are stable under these pullbacks.

When the conditions hold, the gluing morphisms define a descent datum for the modules
`(μ a)^* (O a)` relative to the open cover `g⁻¹ U a` of `Z` (`GlueHom.toDescentData'`).

This is used to glue modules descended to a finite stage of a cofiltered limit of schemes: the
modules `O a` live on (possibly different) stages, and the cocycle conditions only hold after
passing to a later stage.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pseudofunctor LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

section Res

variable {S T Z : Scheme.{u}} {G : T ⟶ S} {g : Z ⟶ S}

@[reassoc (attr := simp)]
lemma resTo_homOfLE (h : Z ⟶ T) (hg : h ≫ G = g) {V V' W : S.Opens} (hWV : W ≤ V)
    (hVV' : V ≤ V') :
    resTo h hg hWV ≫ T.homOfLE (G.preimage_mono hVV') = resTo h hg (hWV.trans hVV') := by
  rw [← cancel_mono (G ⁻¹ᵁ V').ι]
  simp

end Res

variable {S : Scheme.{u}} {ι : Type u} (U : ι → S.Opens) {W : ι → Scheme.{u}}
  (O : ∀ a, modulesPseudofunctor.obj (.mk (op (W a))))

/-- **Gluing morphisms for modules defined on other schemes.** For `g : Z ⟶ S` and morphisms
`μ a : g⁻¹ U a ⟶ W a`, these are morphisms between the pullbacks of `O a` and `O b` to
`g⁻¹ (U a ⊓ U b)` along the composites of the inclusions with `μ a` and `μ b`. -/
abbrev GlueHom {Z : Scheme.{u}} (g : Z ⟶ S) (μ : ∀ a, (g ⁻¹ᵁ U a).toScheme ⟶ W a) :=
  ∀ a b,
    (modulesPseudofunctor.map ((preimageChosenPullback U g a b).p₁ ≫ μ a).op.toLoc).toFunctor.obj
      (O a) ⟶
    (modulesPseudofunctor.map ((preimageChosenPullback U g a b).p₂ ≫ μ b).op.toLoc).toFunctor.obj
      (O b)

section ChosenPullback₃

variable {Z : Scheme.{u}} (g : Z ⟶ S) (a b c : ι)

@[simp]
lemma preimageChosenPullback₃_p₁₂ :
    (preimageChosenPullback₃ U g a b c).p₁₂ = Z.homOfLE (g.preimage_mono inf_le_left) := rfl

@[simp]
lemma preimageChosenPullback₃_p₂₃ :
    (preimageChosenPullback₃ U g a b c).p₂₃ =
      Z.homOfLE (g.preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) := rfl

@[simp]
lemma preimageChosenPullback₃_p₁₃ :
    (preimageChosenPullback₃ U g a b c).p₁₃ =
      Z.homOfLE (g.preimage_mono (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) := rfl

@[simp]
lemma preimageChosenPullback₃_p₂ :
    (preimageChosenPullback₃ U g a b c).p₂ =
      Z.homOfLE (g.preimage_mono (inf_le_left.trans inf_le_right)) := rfl

end ChosenPullback₃

namespace GlueHom

variable {U O} {Z : Scheme.{u}} {g : Z ⟶ S} {μ : ∀ a, (g ⁻¹ᵁ U a).toScheme ⟶ W a}
  (H : GlueHom U O g μ)

/-- The morphism whose equality with the identity is the identity condition on `g⁻¹ U a`. -/
noncomputable def selfLHS (a : ι) :=
  pullHom (H a a) (Z.homOfLE (g.preimage_mono (le_inf le_rfl le_rfl) :
    g ⁻¹ᵁ U a ≤ g ⁻¹ᵁ (U a ⊓ U a))) (μ a) (μ a) (by simp) (by simp)

/-- The left hand side of the cocycle condition on `g⁻¹ (U a ⊓ U b ⊓ U c)`. -/
noncomputable def cocLHS (a b c : ι) :=
  pullHom (H a b) (preimageChosenPullback₃ U g a b c).p₁₂
      ((preimageChosenPullback₃ U g a b c).p₁ ≫ μ a)
      ((preimageChosenPullback₃ U g a b c).p₂ ≫ μ b) (by simp) (by simp) ≫
    pullHom (H b c) (preimageChosenPullback₃ U g a b c).p₂₃
      ((preimageChosenPullback₃ U g a b c).p₂ ≫ μ b)
      ((preimageChosenPullback₃ U g a b c).p₃ ≫ μ c) (by simp) (by simp)

/-- The right hand side of the cocycle condition on `g⁻¹ (U a ⊓ U b ⊓ U c)`. -/
noncomputable def cocRHS (a b c : ι) :=
  pullHom (H a c) (preimageChosenPullback₃ U g a b c).p₁₃
    ((preimageChosenPullback₃ U g a b c).p₁ ≫ μ a)
    ((preimageChosenPullback₃ U g a b c).p₃ ≫ μ c) (by simp) (by simp)

/-- The identity condition for gluing morphisms. -/
def SelfCond : Prop := ∀ a, H.selfLHS a = 𝟙 _

/-- The cocycle condition for gluing morphisms. -/
def CocycleCond : Prop := ∀ a b c, H.cocLHS a b c = H.cocRHS a b c

section Pull

variable {Z' : Scheme.{u}} (h : Z' ⟶ Z) {g' : Z' ⟶ S} (hg : h ≫ g = g')
  {μ' : ∀ a, (g' ⁻¹ᵁ U a).toScheme ⟶ W a} (hμ : ∀ a, resTo h hg le_rfl ≫ μ a = μ' a)

include hμ in
lemma comp_μ_eq {Y : Scheme.{u}} {a : ι} (f₁ : Y ⟶ (g ⁻¹ᵁ U a).toScheme)
    (f₂ : Y ⟶ (g' ⁻¹ᵁ U a).toScheme) (e : f₁ ≫ (g ⁻¹ᵁ U a).ι = f₂ ≫ (g' ⁻¹ᵁ U a).ι ≫ h) :
    f₁ ≫ μ a = f₂ ≫ μ' a := by
  rw [← hμ, ← Category.assoc]
  congr 1
  rw [← cancel_mono (g ⁻¹ᵁ U a).ι, e]
  simp

/-- The pullback of gluing morphisms along a morphism `h : Z' ⟶ Z` over `S`. -/
noncomputable def pull : GlueHom U O g' μ' := fun a b ↦
  pullHom (H a b) (resTo h hg le_rfl) _ _
    (by rw [← Category.assoc]; exact comp_μ_eq h hg hμ _ _ (by simp))
    (by rw [← Category.assoc]; exact comp_μ_eq h hg hμ _ _ (by simp))

lemma pull_apply (a b : ι) :
    H.pull h hg hμ a b = pullHom (H a b) (resTo h hg le_rfl) _ _
      (by rw [← Category.assoc]; exact comp_μ_eq h hg hμ _ _ (by simp))
    (by rw [← Category.assoc]; exact comp_μ_eq h hg hμ _ _ (by simp)) := rfl

lemma pull_selfLHS (a : ι) :
    pullHom (H.selfLHS a) (resTo h hg le_rfl) (μ' a) (μ' a) (hμ a) (hμ a) =
      (H.pull h hg hμ).selfLHS a := by
  rw [selfLHS, selfLHS, pull_apply, pullHom_pullHom, pullHom_pullHom]
  exact pullHom_congr_left _ (by rw [← cancel_mono (g ⁻¹ᵁ (U a ⊓ U a)).ι]; simp) _ _ _ _

lemma pull_cocLHS (a b c : ι) :
    pullHom (H.cocLHS a b c) (resTo h hg le_rfl)
        ((preimageChosenPullback₃ U g' a b c).p₁ ≫ μ' a)
        ((preimageChosenPullback₃ U g' a b c).p₃ ≫ μ' c)
        (by rw [← Category.assoc]; exact comp_μ_eq h hg hμ _ _ (by simp))
        (by rw [← Category.assoc]; exact comp_μ_eq h hg hμ _ _ (by simp)) =
      (H.pull h hg hμ).cocLHS a b c := by
  rw [cocLHS, cocLHS, pull_apply, pull_apply]
  refine (pullHom_comp _ _ _ _ ((preimageChosenPullback₃ U g' a b c).p₂ ≫ μ' b) _ _ ?_ _).trans ?_
  · rw [← Category.assoc]
    exact comp_μ_eq h hg hμ _ _ (by simp)
  rw [pullHom_pullHom, pullHom_pullHom, pullHom_pullHom, pullHom_pullHom]
  exact congrArg₂ (· ≫ ·)
    (pullHom_congr_left _ (by rw [← cancel_mono (g ⁻¹ᵁ (U a ⊓ U b)).ι]; simp) _ _ _ _)
    (pullHom_congr_left _ (by rw [← cancel_mono (g ⁻¹ᵁ (U b ⊓ U c)).ι]; simp) _ _ _ _)

lemma pull_cocRHS (a b c : ι) :
    pullHom (H.cocRHS a b c) (resTo h hg le_rfl)
        ((preimageChosenPullback₃ U g' a b c).p₁ ≫ μ' a)
        ((preimageChosenPullback₃ U g' a b c).p₃ ≫ μ' c)
        (by rw [← Category.assoc]; exact comp_μ_eq h hg hμ _ _ (by simp))
        (by rw [← Category.assoc]; exact comp_μ_eq h hg hμ _ _ (by simp)) =
      (H.pull h hg hμ).cocRHS a b c := by
  rw [cocRHS, cocRHS, pull_apply, pullHom_pullHom, pullHom_pullHom]
  exact pullHom_congr_left _ (by
    rw [← cancel_mono (g ⁻¹ᵁ (U a ⊓ U c)).ι]; simp) _ _ _ _

variable {H} in
lemma SelfCond.pull (hH : H.SelfCond) : (H.pull h hg hμ).SelfCond := fun a ↦ by
  rw [← pull_selfLHS, hH a, pullHom_id_eq_id]

variable {H} in
lemma CocycleCond.pull (hH : H.CocycleCond) : (H.pull h hg hμ).CocycleCond := fun a b c ↦ by
  rw [← pull_cocLHS, ← pull_cocRHS, hH a b c]

end Pull

section ToPreGlue

/-- Morphisms conjugated by the components of comparison isomorphisms `mapComp'` agree if and
only if the original morphisms agree. -/
lemma mapComp'_conj_inj {X₁ X₂ Y₁ Y₂ Y : Scheme.{u}} {M₁ : modulesPseudofunctor.obj (.mk (op X₁))}
    {M₂ : modulesPseudofunctor.obj (.mk (op X₂))} (r₁ : Y₁ ⟶ X₁) (r₂ : Y₂ ⟶ X₂) (p₁ : Y ⟶ Y₁)
    (p₂ : Y ⟶ Y₂) (x₁ : Y ⟶ X₁) (x₂ : Y ⟶ X₂) (hx₁ : p₁ ≫ r₁ = x₁) (hx₂ : p₂ ≫ r₂ = x₂)
    (φ ψ : (modulesPseudofunctor.map x₁.op.toLoc).toFunctor.obj M₁ ⟶
      (modulesPseudofunctor.map x₂.op.toLoc).toFunctor.obj M₂) :
    (modulesPseudofunctor.mapComp' r₁.op.toLoc p₁.op.toLoc x₁.op.toLoc
        (op_toLoc_comp_eq hx₁)).inv.toNatTrans.app M₁ ≫ φ ≫
      (modulesPseudofunctor.mapComp' r₂.op.toLoc p₂.op.toLoc x₂.op.toLoc
        (op_toLoc_comp_eq hx₂)).hom.toNatTrans.app M₂ =
    (modulesPseudofunctor.mapComp' r₁.op.toLoc p₁.op.toLoc x₁.op.toLoc
        (op_toLoc_comp_eq hx₁)).inv.toNatTrans.app M₁ ≫ ψ ≫
      (modulesPseudofunctor.mapComp' r₂.op.toLoc p₂.op.toLoc x₂.op.toLoc
        (op_toLoc_comp_eq hx₂)).hom.toNatTrans.app M₂ ↔ φ = ψ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have := congr((modulesPseudofunctor.mapComp' r₁.op.toLoc p₁.op.toLoc x₁.op.toLoc
        (op_toLoc_comp_eq hx₁)).hom.toNatTrans.app M₁ ≫ $h ≫
      (modulesPseudofunctor.mapComp' r₂.op.toLoc p₂.op.toLoc x₂.op.toLoc
        (op_toLoc_comp_eq hx₂)).inv.toNatTrans.app M₂)
  simpa using this

/-- The gluing data for the modules `(μ a)^* (O a)` on the opens `g⁻¹ U a`, obtained by
conjugating gluing morphisms with the comparison isomorphisms `mapComp'`. -/
noncomputable def toPreGlue : PreGlueData U g where
  obj a := (modulesPseudofunctor.map (μ a).op.toLoc).toFunctor.obj (O a)
  hom a b :=
    (modulesPseudofunctor.mapComp' (μ a).op.toLoc (preimageChosenPullback U g a b).p₁.op.toLoc
      ((preimageChosenPullback U g a b).p₁ ≫ μ a).op.toLoc
      (op_toLoc_comp_eq rfl)).inv.toNatTrans.app (O a) ≫ H a b ≫
    (modulesPseudofunctor.mapComp' (μ b).op.toLoc (preimageChosenPullback U g a b).p₂.op.toLoc
      ((preimageChosenPullback U g a b).p₂ ≫ μ b).op.toLoc
      (op_toLoc_comp_eq rfl)).hom.toNatTrans.app (O b)

lemma toPreGlue_selfMor (a : ι) :
    H.toPreGlue.selfMor a =
      (modulesPseudofunctor.mapComp' (μ a).op.toLoc (𝟙 _ : (g ⁻¹ᵁ U a).toScheme ⟶ _).op.toLoc
        (μ a).op.toLoc (op_toLoc_comp_eq (Category.id_comp _))).inv.toNatTrans.app (O a) ≫
        H.selfLHS a ≫
      (modulesPseudofunctor.mapComp' (μ a).op.toLoc (𝟙 _ : (g ⁻¹ᵁ U a).toScheme ⟶ _).op.toLoc
        (μ a).op.toLoc (op_toLoc_comp_eq (Category.id_comp _))).hom.toNatTrans.app (O a) := by
  rw [PreGlueData.selfMor, DescentData'.pullHom'_eq_pullHom _ _ _ _
    (Z.homOfLE (g.preimage_mono (le_inf le_rfl le_rfl) : g ⁻¹ᵁ U a ≤ g ⁻¹ᵁ (U a ⊓ U a)))
    (by simp) (by simp) (by simp) (by simp)]
  exact pullHom_mapComp'_conj _ _ _ _ _ _ rfl rfl (H a a) _ _ _ (by simp) (by simp) _ _
    (Category.id_comp _) (Category.id_comp _)

lemma toPreGlue_cocycleLeft (a b c : ι) :
    H.toPreGlue.cocycleLeft a b c =
      (modulesPseudofunctor.mapComp' (μ a).op.toLoc
        (preimageChosenPullback₃ U g a b c).p₁.op.toLoc
        ((preimageChosenPullback₃ U g a b c).p₁ ≫ μ a).op.toLoc
        (op_toLoc_comp_eq rfl)).inv.toNatTrans.app (O a) ≫ H.cocLHS a b c ≫
      (modulesPseudofunctor.mapComp' (μ c).op.toLoc
        (preimageChosenPullback₃ U g a b c).p₃.op.toLoc
        ((preimageChosenPullback₃ U g a b c).p₃ ≫ μ c).op.toLoc
        (op_toLoc_comp_eq rfl)).hom.toNatTrans.app (O c) := by sorry

lemma toPreGlue_cocycleRight (a b c : ι) :
    H.toPreGlue.cocycleRight a b c =
      (modulesPseudofunctor.mapComp' (μ a).op.toLoc
        (preimageChosenPullback₃ U g a b c).p₁.op.toLoc
        ((preimageChosenPullback₃ U g a b c).p₁ ≫ μ a).op.toLoc
        (op_toLoc_comp_eq rfl)).inv.toNatTrans.app (O a) ≫ H.cocRHS a b c ≫
      (modulesPseudofunctor.mapComp' (μ c).op.toLoc
        (preimageChosenPullback₃ U g a b c).p₃.op.toLoc
        ((preimageChosenPullback₃ U g a b c).p₃ ≫ μ c).op.toLoc
        (op_toLoc_comp_eq rfl)).hom.toNatTrans.app (O c) := by sorry

lemma isCocycle_toPreGlue_iff : H.toPreGlue.IsCocycle ↔ H.SelfCond ∧ H.CocycleCond := by sorry

end ToPreGlue

end GlueHom

end AlgebraicGeometry.Scheme.Modules
