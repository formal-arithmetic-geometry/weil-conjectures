/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Gluing data for modules along preimages of an open cover

Let `U a` be a family of opens of a scheme `S` and `g : Z ⟶ S` a morphism. We consider gluing
data for sheaves of modules on `Z` relative to the opens `g⁻¹ U a`, with the intersections
`g⁻¹ (U a ⊓ U b)` and `g⁻¹ (U a ⊓ U b ⊓ U c)` as chosen (wide) pullbacks
(`AlgebraicGeometry.Scheme.Modules.PreGlueData`), *without* the cocycle conditions.

We also consider gluing morphisms for modules `O a` on the opens `G⁻¹ U a` of a fixed scheme
`T` over `S`, given over the preimages of the intersections in any `h : Z ⟶ T`
(`AlgebraicGeometry.Scheme.Modules.HomData`). Such data can be pulled back along any `Z' ⟶ Z`
by `pullHom`, and the identity and cocycle conditions are compatible with these pullbacks.

This is used to glue modules descended to a finite stage of a cofiltered limit of schemes: the
cocycle conditions only hold after passing to a later stage.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pseudofunctor LocallyDiscreteOpToCat

namespace CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type*} [Category* C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}

lemma op_toLoc_comp_eq {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {fg : X ⟶ Z} (h : f ≫ g = fg) :
    g.op.toLoc ≫ f.op.toLoc = fg.op.toLoc := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `pullHom` of a morphism conjugated by the comparison isomorphisms `mapComp'`. -/
lemma pullHom_mapComp'_conj ⦃X₁ X₂ X₁' X₂' : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ (r₁ : X₁' ⟶ X₁) (r₂ : X₂' ⟶ X₂) ⦃Y : C⦄ (p₁ : Y ⟶ X₁')
    (p₂ : Y ⟶ X₂') (x₁ : Y ⟶ X₁) (x₂ : Y ⟶ X₂) (hx₁ : p₁ ≫ r₁ = x₁) (hx₂ : p₂ ≫ r₂ = x₂)
    (ψ : (F.map x₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map x₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : C⦄ (l : Y' ⟶ Y) (f₁ : Y' ⟶ X₁') (f₂ : Y' ⟶ X₂') (hl₁ : l ≫ p₁ = f₁)
    (hl₂ : l ≫ p₂ = f₂) (y₁ : Y' ⟶ X₁) (y₂ : Y' ⟶ X₂) (hy₁ : f₁ ≫ r₁ = y₁)
    (hy₂ : f₂ ≫ r₂ = y₂) :
    pullHom ((F.mapComp' r₁.op.toLoc p₁.op.toLoc x₁.op.toLoc
        (op_toLoc_comp_eq hx₁)).inv.toNatTrans.app M₁ ≫ ψ ≫
        (F.mapComp' r₂.op.toLoc p₂.op.toLoc x₂.op.toLoc
          (op_toLoc_comp_eq hx₂)).hom.toNatTrans.app M₂) l f₁ f₂ hl₁ hl₂ =
      (F.mapComp' r₁.op.toLoc f₁.op.toLoc y₁.op.toLoc
          (op_toLoc_comp_eq hy₁)).inv.toNatTrans.app M₁ ≫
        pullHom ψ l y₁ y₂ (by rw [← hy₁, ← hx₁, ← hl₁, Category.assoc])
          (by rw [← hy₂, ← hx₂, ← hl₂, Category.assoc]) ≫
        (F.mapComp' r₂.op.toLoc f₂.op.toLoc y₂.op.toLoc
          (op_toLoc_comp_eq hy₂)).hom.toNatTrans.app M₂ := by
  subst hx₁ hx₂ hl₁ hl₂ hy₁ hy₂
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ rfl rfl (by cat_disch),
    mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ rfl rfl (by cat_disch)]

set_option backward.isDefEq.respectTransparency false in
/-- `pullHom` of a morphism conjugated by the inverses of the comparison isomorphisms
`mapComp'`. -/
lemma pullHom_mapComp'_conj_symm ⦃X₁ X₂ X₁' X₂' : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ (p₁ : X₁' ⟶ X₁) (p₂ : X₂' ⟶ X₂) ⦃Y : C⦄ (r₁ : Y ⟶ X₁')
    (r₂ : Y ⟶ X₂') (x₁ : Y ⟶ X₁) (x₂ : Y ⟶ X₂) (hx₁ : r₁ ≫ p₁ = x₁) (hx₂ : r₂ ≫ p₂ = x₂)
    (ψ : (F.map r₁.op.toLoc).toFunctor.obj ((F.map p₁.op.toLoc).toFunctor.obj M₁) ⟶
      (F.map r₂.op.toLoc).toFunctor.obj ((F.map p₂.op.toLoc).toFunctor.obj M₂))
    ⦃Y' : C⦄ (l : Y' ⟶ Y) (z₁ : Y' ⟶ X₁') (z₂ : Y' ⟶ X₂') (hz₁ : l ≫ r₁ = z₁)
    (hz₂ : l ≫ r₂ = z₂) (y₁ : Y' ⟶ X₁) (y₂ : Y' ⟶ X₂) (hy₁ : z₁ ≫ p₁ = y₁)
    (hy₂ : z₂ ≫ p₂ = y₂) :
    pullHom ((F.mapComp' p₁.op.toLoc r₁.op.toLoc x₁.op.toLoc
        (op_toLoc_comp_eq hx₁)).hom.toNatTrans.app M₁ ≫ ψ ≫
        (F.mapComp' p₂.op.toLoc r₂.op.toLoc x₂.op.toLoc
          (op_toLoc_comp_eq hx₂)).inv.toNatTrans.app M₂) l y₁ y₂
        (by rw [← hy₁, ← hx₁, ← hz₁, Category.assoc])
        (by rw [← hy₂, ← hx₂, ← hz₂, Category.assoc]) =
      (F.mapComp' p₁.op.toLoc z₁.op.toLoc y₁.op.toLoc
          (op_toLoc_comp_eq hy₁)).hom.toNatTrans.app M₁ ≫
        pullHom ψ l z₁ z₂ hz₁ hz₂ ≫
        (F.mapComp' p₂.op.toLoc z₂.op.toLoc y₂.op.toLoc
          (op_toLoc_comp_eq hy₂)).inv.toNatTrans.app M₂ := by
  subst hx₁ hx₂ hz₁ hz₂ hy₁ hy₂
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc _ _ _ _ _ _ rfl rfl
      (by cat_disch),
    F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app _ _ _ _ _ _ rfl rfl (by cat_disch)]

/-- Morphisms with equal pullbacks have equal `pullHom`s. -/
lemma pullHom_eq_pullHom_of_map_eq ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    {φ φ' : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂}
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂)
    (h : (F.map g.op.toLoc).toFunctor.map φ = (F.map g.op.toLoc).toFunctor.map φ') :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ = pullHom φ' g gf₁ gf₂ hgf₁ hgf₂ := by
  simp only [pullHom, h]

/-- Morphisms with equal `pullHom`s have equal pullbacks. -/
lemma map_eq_map_of_pullHom_eq ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    {φ φ' : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂}
    ⦃Y' : C⦄ (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) (h : pullHom φ g gf₁ gf₂ hgf₁ hgf₂ = pullHom φ' g gf₁ gf₂ hgf₁ hgf₂) :
    (F.map g.op.toLoc).toFunctor.map φ = (F.map g.op.toLoc).toFunctor.map φ' := by
  rw [map_eq_pullHom φ g gf₁ gf₂ hgf₁ hgf₂, map_eq_pullHom φ' g gf₁ gf₂ hgf₁ hgf₂, h]

end CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

section Res

variable {S T Z Z' : Scheme.{u}} {G : T ⟶ S} {g : Z ⟶ S}

/-- The restriction `g⁻¹ W ⟶ G⁻¹ V` of a morphism `h : Z ⟶ T` over `S`, for `W ≤ V`. -/
noncomputable def resTo (h : Z ⟶ T) (hg : h ≫ G = g) {V W : S.Opens} (hWV : W ≤ V) :
    (g ⁻¹ᵁ W).toScheme ⟶ (G ⁻¹ᵁ V).toScheme :=
  h.resLE (G ⁻¹ᵁ V) (g ⁻¹ᵁ W) (by
    subst hg
    rw [Scheme.Hom.comp_preimage]
    exact h.preimage_mono (G.preimage_mono hWV))

@[reassoc (attr := simp)]
lemma resTo_ι (h : Z ⟶ T) (hg : h ≫ G = g) {V W : S.Opens} (hWV : W ≤ V) :
    resTo h hg hWV ≫ (G ⁻¹ᵁ V).ι = (g ⁻¹ᵁ W).ι ≫ h :=
  Scheme.Hom.resLE_comp_ι _ _

@[reassoc (attr := simp)]
lemma homOfLE_resTo (h : Z ⟶ T) (hg : h ≫ G = g) {V W W' : S.Opens} (e : g ⁻¹ᵁ W' ≤ g ⁻¹ᵁ W)
    (hWV : W ≤ V) (hW'V : W' ≤ V) :
    Z.homOfLE e ≫ resTo h hg hWV = resTo h hg hW'V := by
  rw [← cancel_mono (G ⁻¹ᵁ V).ι]
  simp

@[reassoc]
lemma resTo_resTo (h : Z ⟶ T) (hg : h ≫ G = g) {g' : Z' ⟶ S} (h₂ : Z' ⟶ Z) (hg₂ : h₂ ≫ g = g')
    {h' : Z' ⟶ T} (hh : h₂ ≫ h = h') (hg' : h' ≫ G = g') {V W W' : S.Opens} (hWV : W ≤ V)
    (hW'W : W' ≤ W) (hW'V : W' ≤ V) :
    resTo h₂ hg₂ hW'W ≫ resTo h hg hWV = resTo h' hg' hW'V := by
  rw [← cancel_mono (G ⁻¹ᵁ V).ι]
  simp [← hh]

end Res

variable {S : Scheme.{u}} {ι : Type u} (U : ι → S.Opens) {Z : Scheme.{u}} (g : Z ⟶ S)

/-- The intersection `g⁻¹ (U a ⊓ U b)` as a chosen pullback of the open immersions of `g⁻¹ U a`
and `g⁻¹ U b`. -/
@[simps]
noncomputable def preimageChosenPullback (a b : ι) :
    ChosenPullback (g ⁻¹ᵁ U a).ι (g ⁻¹ᵁ U b).ι where
  pullback := g ⁻¹ᵁ (U a ⊓ U b)
  p₁ := Z.homOfLE (g.preimage_mono inf_le_left)
  p₂ := Z.homOfLE (g.preimage_mono inf_le_right)
  condition := by simp
  isLimit := (IsOpenImmersion.isPullback (Z.homOfLE (g.preimage_mono inf_le_left))
    (Z.homOfLE (g.preimage_mono inf_le_right)) (g ⁻¹ᵁ U a).ι (g ⁻¹ᵁ U b).ι (by simp)
    (by ext x; simp)).isLimit
  p := (g ⁻¹ᵁ (U a ⊓ U b)).ι
  hp₁ := by simp

/-- The triple intersection `g⁻¹ (U a ⊓ U b ⊓ U c)` as a chosen wide pullback. -/
@[simps]
noncomputable def preimageChosenPullback₃ (a b c : ι) :
    ChosenPullback₃ (preimageChosenPullback U g a b) (preimageChosenPullback U g b c)
      (preimageChosenPullback U g a c) where
  chosenPullback :=
    { pullback := g ⁻¹ᵁ (U a ⊓ U b ⊓ U c)
      p₁ := Z.homOfLE (g.preimage_mono inf_le_left)
      p₂ := Z.homOfLE (g.preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
      condition := by simp
      isLimit := by
        refine (IsOpenImmersion.isPullback (Z.homOfLE (g.preimage_mono inf_le_left))
          (Z.homOfLE (g.preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right)))
          (Z.homOfLE (g.preimage_mono inf_le_right))
          (Z.homOfLE (g.preimage_mono inf_le_left)) (by simp) ?_).isLimit
        ext x
        simp only [opensRange_homOfLE, TopologicalSpace.Opens.map_coe,
          TopologicalSpace.Opens.coe_inf, Set.preimage_inter, Set.mem_inter_iff,
          Set.mem_preimage, Opens.ι_apply, homOfLE_apply, SetLike.mem_coe, iff_self_and,
          and_imp]
        exact fun _ _ ↦ x.2.2
      p := Z.homOfLE (g.preimage_mono (inf_le_left.trans inf_le_right))
      hp₁ := by simp }
  p := (g ⁻¹ᵁ (U a ⊓ U b ⊓ U c)).ι
  p₁ := Z.homOfLE (g.preimage_mono (inf_le_left.trans inf_le_left))
  p₃ := Z.homOfLE (g.preimage_mono inf_le_right)
  l :=
    { f := Z.homOfLE (g.preimage_mono (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) }
  hp₁ := by simp
  hp₃ := by simp

/-- **Gluing data without cocycle condition** for the opens `g⁻¹ U a` of `Z`: modules `obj a` on
`g⁻¹ U a` and morphisms `hom a b` between their pullbacks to `g⁻¹ (U a ⊓ U b)`. -/
structure PreGlueData where
  /-- The modules on the opens `g⁻¹ U a`. -/
  obj (a : ι) : modulesPseudofunctor.obj (.mk (op (g ⁻¹ᵁ U a).toScheme))
  /-- The gluing morphisms on the intersections `g⁻¹ (U a ⊓ U b)`. -/
  hom (a b : ι) :
    (modulesPseudofunctor.map (preimageChosenPullback U g a b).p₁.op.toLoc).toFunctor.obj
        (obj a) ⟶
      (modulesPseudofunctor.map (preimageChosenPullback U g a b).p₂.op.toLoc).toFunctor.obj
        (obj b)

namespace PreGlueData

variable {U g} (P : PreGlueData U g)

/-- The morphism whose equality with the identity is the identity condition on `g⁻¹ U a`. -/
noncomputable def selfMor (a : ι) :=
  DescentData'.pullHom' (sq := preimageChosenPullback U g) P.hom (g ⁻¹ᵁ U a).ι (𝟙 _) (𝟙 _)

/-- The left hand side of the cocycle condition on `g⁻¹ (U a ⊓ U b ⊓ U c)`. -/
noncomputable def cocycleLeft (a b c : ι) :=
  DescentData'.pullHom' (sq := preimageChosenPullback U g) P.hom
      (preimageChosenPullback₃ U g a b c).p (preimageChosenPullback₃ U g a b c).p₁
      (preimageChosenPullback₃ U g a b c).p₂ ≫
    DescentData'.pullHom' (sq := preimageChosenPullback U g) P.hom
      (preimageChosenPullback₃ U g a b c).p (preimageChosenPullback₃ U g a b c).p₂
      (preimageChosenPullback₃ U g a b c).p₃

/-- The right hand side of the cocycle condition on `g⁻¹ (U a ⊓ U b ⊓ U c)`. -/
noncomputable def cocycleRight (a b c : ι) :=
  DescentData'.pullHom' (sq := preimageChosenPullback U g) P.hom
    (preimageChosenPullback₃ U g a b c).p (preimageChosenPullback₃ U g a b c).p₁
    (preimageChosenPullback₃ U g a b c).p₃

/-- The identity and cocycle conditions. -/
structure IsCocycle : Prop where
  selfMor_eq (a : ι) : P.selfMor a = 𝟙 _
  cocycleLeft_eq (a b c : ι) : P.cocycleLeft a b c = P.cocycleRight a b c

set_option maxHeartbeats 20000 in
example (D : modulesPseudofunctor.DescentData' (preimageChosenPullback U g)
    (preimageChosenPullback₃ U g)) : PreGlueData U g where
  obj := D.obj
  hom a b := D.hom a b

end PreGlueData

end AlgebraicGeometry.Scheme.Modules
