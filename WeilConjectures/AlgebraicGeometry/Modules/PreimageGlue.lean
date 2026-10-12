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
(`AlgebraicGeometry.Scheme.Modules.PreGlueData`), *without* the cocycle conditions. Such data can
be pulled back along any `h : Z' ⟶ Z` (`AlgebraicGeometry.Scheme.Modules.PreGlueData.pull`), and
the cocycle conditions for the pulled back data are the pullbacks along the restrictions of `h`
of the cocycle conditions for the original data.

This is used to glue modules descended to a finite stage of a cofiltered limit of schemes: the
cocycle conditions only hold after passing to a later stage.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pseudofunctor LocallyDiscreteOpToCat

namespace CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type*} [Category* C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}

set_option backward.isDefEq.respectTransparency false in
/-- `pullHom` of a morphism conjugated by the comparison isomorphisms `mapComp'`. -/
lemma pullHom_mapComp'_conj ⦃X₁ X₂ X₁' X₂' : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ (r₁ : X₁' ⟶ X₁) (r₂ : X₂' ⟶ X₂) ⦃Y : C⦄ (p₁ : Y ⟶ X₁')
    (p₂ : Y ⟶ X₂') (x₁ : Y ⟶ X₁) (x₂ : Y ⟶ X₂) (hx₁ : p₁ ≫ r₁ = x₁) (hx₂ : p₂ ≫ r₂ = x₂)
    (ψ : (F.map x₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map x₂.op.toLoc).toFunctor.obj M₂)
    ⦃Y' : C⦄ (l : Y' ⟶ Y) (f₁ : Y' ⟶ X₁') (f₂ : Y' ⟶ X₂') (hl₁ : l ≫ p₁ = f₁)
    (hl₂ : l ≫ p₂ = f₂) :
    pullHom ((F.mapComp' r₁.op.toLoc p₁.op.toLoc x₁.op.toLoc (by subst hx₁; rfl)).inv.toNatTrans.app
        M₁ ≫ ψ ≫
        (F.mapComp' r₂.op.toLoc p₂.op.toLoc x₂.op.toLoc (by subst hx₂; rfl)).hom.toNatTrans.app
          M₂) l f₁ f₂ hl₁ hl₂ =
      (F.mapComp' r₁.op.toLoc f₁.op.toLoc (f₁ ≫ r₁).op.toLoc rfl).inv.toNatTrans.app M₁ ≫
        pullHom ψ l (f₁ ≫ r₁) (f₂ ≫ r₂) (by rw [← hx₁, ← hl₁, Category.assoc])
          (by rw [← hx₂, ← hl₂, Category.assoc]) ≫
        (F.mapComp' r₂.op.toLoc f₂.op.toLoc (f₂ ≫ r₂).op.toLoc rfl).hom.toNatTrans.app M₂ := by
  subst hx₁ hx₂ hl₁ hl₂
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ rfl rfl (by cat_disch),
    mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ rfl rfl (by cat_disch)]

end CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

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
        simp
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

/-- Gluing data satisfying the cocycle conditions, as descent data relative to the chosen
pullbacks. -/
set_option maxHeartbeats 2000000 in
noncomputable def toDescentData' (hP : P.IsCocycle) :
    modulesPseudofunctor.DescentData' (preimageChosenPullback U g)
      (preimageChosenPullback₃ U g) where
  obj := P.obj
  hom := P.hom
  pullHom'_hom_self := hP.selfMor_eq
  pullHom'_hom_comp a b c := by
    have := hP.cocycleLeft_eq a b c
    unfold cocycleLeft cocycleRight at this
    exact this

/-- Descent data relative to the chosen pullbacks, as gluing data. -/
def ofDescentData' (D : modulesPseudofunctor.DescentData' (preimageChosenPullback U g)
    (preimageChosenPullback₃ U g)) : PreGlueData U g where
  obj := D.obj
  hom := D.hom

lemma isCocycle_ofDescentData' (D : modulesPseudofunctor.DescentData'
    (preimageChosenPullback U g) (preimageChosenPullback₃ U g)) :
    (ofDescentData' D).IsCocycle where
  selfMor_eq := D.pullHom'_hom_self
  cocycleLeft_eq := D.pullHom'_hom_comp

section Pull

variable {Z' : Scheme.{u}} (h : Z' ⟶ Z) {g' : Z' ⟶ S} (hg : h ≫ g = g')

/-- The restriction `g'⁻¹ O ⟶ g⁻¹ O` of `h : Z' ⟶ Z`, for `h ≫ g = g'`. -/
noncomputable def preimageRes (O : S.Opens) : (g' ⁻¹ᵁ O).toScheme ⟶ (g ⁻¹ᵁ O).toScheme :=
  h.resLE (g ⁻¹ᵁ O) (g' ⁻¹ᵁ O) (by subst hg; rw [Scheme.Hom.comp_preimage])

@[reassoc (attr := simp)]
lemma preimageRes_ι (O : S.Opens) : preimageRes h hg O ≫ (g ⁻¹ᵁ O).ι = (g' ⁻¹ᵁ O).ι ≫ h := by
  simp [preimageRes]

@[reassoc (attr := simp)]
lemma homOfLE_preimageRes {O O' : S.Opens} (hO : O ≤ O') :
    Z'.homOfLE (g'.preimage_mono hO) ≫ preimageRes h hg O' =
      preimageRes h hg O ≫ Z.homOfLE (g.preimage_mono hO) := by
  simp [preimageRes]

/-- The pullback of gluing data along `h : Z' ⟶ Z`. -/
noncomputable def pull : PreGlueData U g' where
  obj a := (modulesPseudofunctor.map (preimageRes h hg (U a)).op.toLoc).toFunctor.obj (P.obj a)
  hom a b :=
    (modulesPseudofunctor.mapComp' (preimageRes h hg (U a)).op.toLoc
      (preimageChosenPullback U g' a b).p₁.op.toLoc
      (preimageRes h hg (U a ⊓ U b) ≫ (preimageChosenPullback U g a b).p₁).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]; simp)).inv.toNatTrans.app (P.obj a) ≫
    pullHom (P.hom a b) (preimageRes h hg (U a ⊓ U b)) _ _ rfl rfl ≫
    (modulesPseudofunctor.mapComp' (preimageRes h hg (U b)).op.toLoc
      (preimageChosenPullback U g' a b).p₂.op.toLoc
      (preimageRes h hg (U a ⊓ U b) ≫ (preimageChosenPullback U g a b).p₂).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp]; simp)).hom.toNatTrans.app (P.obj b)

/-- **Pulled back gluing morphisms**: the gluing morphisms of `P.pull h hg`, pulled back along
any `f₁, f₂`, are those of `P` pulled back along the composites with the restrictions of `h`. -/
lemma pullHom'_pull ⦃Y : Scheme.{u}⦄ (q : Y ⟶ Z') ⦃a b : ι⦄ (f₁ : Y ⟶ (g' ⁻¹ᵁ U a).toScheme)
    (f₂ : Y ⟶ (g' ⁻¹ᵁ U b).toScheme) (hf₁ : f₁ ≫ (g' ⁻¹ᵁ U a).ι = q)
    (hf₂ : f₂ ≫ (g' ⁻¹ᵁ U b).ι = q) (q' : Y ⟶ Z) (hq : q ≫ h = q')
    (x₁ : Y ⟶ (g ⁻¹ᵁ U a).toScheme) (x₂ : Y ⟶ (g ⁻¹ᵁ U b).toScheme)
    (hx₁ : f₁ ≫ preimageRes h hg (U a) = x₁) (hx₂ : f₂ ≫ preimageRes h hg (U b) = x₂) :
    DescentData'.pullHom' (P.pull h hg).hom q f₁ f₂ hf₁ hf₂ =
      (modulesPseudofunctor.mapComp' (preimageRes h hg (U a)).op.toLoc f₁.op.toLoc x₁.op.toLoc
        (by subst hx₁; rfl)).inv.toNatTrans.app (P.obj a) ≫
      DescentData'.pullHom' P.hom q' x₁ x₂ (by subst hx₁ hq hf₁; simp)
        (by subst hx₂ hq hf₂; simp) ≫
      (modulesPseudofunctor.mapComp' (preimageRes h hg (U b)).op.toLoc f₂.op.toLoc x₂.op.toLoc
        (by subst hx₂; rfl)).hom.toNatTrans.app (P.obj b) := by
  sorry

end Pull

end PreGlueData

end AlgebraicGeometry.Scheme.Modules
