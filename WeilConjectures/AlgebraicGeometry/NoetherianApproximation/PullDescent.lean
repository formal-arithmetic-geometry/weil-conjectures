/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Descent data obtained by pulling back gluing data along a morphism

Let `S` be a scheme covered by opens `U a` and suppose given modules `obj a` on `U a` together
with morphisms `hom a b : (obj a)|_{U a ∩ U b} ⟶ (obj b)|_{U a ∩ U b}`, without any cocycle
condition (`AlgebraicGeometry.Scheme.Modules.PreDescentData`). For a morphism `ρ : T ⟶ S` the
pullbacks of `obj a` to the opens `ρ⁻¹ U a` of `T`, together with the pullbacks of the `hom a b`,
form a descent datum relative to the family of open immersions `ρ⁻¹ U a ⟶ T` as soon as the
identity and cocycle conditions hold after pullback along `ρ` over the opens `U a` and the triple
intersections `U a ∩ U b ∩ U c` (`AlgebraicGeometry.Scheme.Modules.PreDescentData.descentData`).

This is used to glue modules descended to a finite stage of a cofiltered limit of schemes: the
cocycle conditions only hold after passing to a later stage.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pseudofunctor LocallyDiscreteOpToCat

namespace CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type*} [Category* C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pullHom_comp ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃M₃ : F.obj (.mk (op X₃))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃) (hgf₁ : g ≫ f₁ = gf₁)
    (hgf₂ : g ≫ f₂ = gf₂) (hgf₃ : g ≫ f₃ = gf₃) :
    pullHom (φ ≫ ψ) g gf₁ gf₃ hgf₁ hgf₃ =
      pullHom φ g gf₁ gf₂ hgf₁ hgf₂ ≫ pullHom ψ g gf₂ gf₃ hgf₂ hgf₃ := by
  simp [pullHom]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma pullHom_id' ⦃X₁ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (hgf₁ : g ≫ f₁ = gf₁) :
    pullHom (𝟙 ((F.map f₁.op.toLoc).toFunctor.obj M₁)) g gf₁ gf₁ hgf₁ hgf₁ = 𝟙 _ := by
  simp [pullHom]

end CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

/-- **Gluing data without cocycle condition.** Modules `obj a` on the members `U a` of a family
of opens of `S`, and morphisms `hom a b` between their pullbacks to `U a ∩ U b`. -/
structure PreDescentData {S : Scheme.{u}} {ι : Type*} (U : ι → S.Opens) where
  /-- The modules on the opens `U a`. -/
  obj (a : ι) : modulesPseudofunctor.obj (.mk (op (U a).toScheme))
  /-- The gluing morphisms on the intersections `U a ∩ U b`. -/
  hom (a b : ι) :
    (modulesPseudofunctor.map (S.homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op.toLoc).toFunctor.obj
        (obj a) ⟶
      (modulesPseudofunctor.map
        (S.homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op.toLoc).toFunctor.obj (obj b)

namespace PreDescentData

variable {S T : Scheme.{u}} {ι : Type*} {U : ι → S.Opens} (D : PreDescentData U) (ρ : T ⟶ S)

/-- The morphism to `U a ∩ U b` from a scheme with maps to `ρ⁻¹ U a` and `ρ⁻¹ U b` over `T`. -/
noncomputable def lift {Y : Scheme.{u}} {a b : ι} (f₁ : Y ⟶ (ρ ⁻¹ᵁ U a).toScheme)
    (f₂ : Y ⟶ (ρ ⁻¹ᵁ U b).toScheme) (h : f₁ ≫ (ρ ⁻¹ᵁ U a).ι = f₂ ≫ (ρ ⁻¹ᵁ U b).ι) :
    Y ⟶ (U a ⊓ U b).toScheme :=
  IsOpenImmersion.lift (U a ⊓ U b).ι (f₁ ≫ (ρ ⁻¹ᵁ U a).ι ≫ ρ) (by
    rintro _ ⟨y, rfl⟩
    have e : ((f₁ y).1 : T) = (f₂ y).1 := by
      have := congr(($h).base y)
      simpa using this
    rw [Scheme.Opens.range_ι]
    simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    exact ⟨(f₁ y).2, by rw [e]; exact (f₂ y).2⟩)


@[reassoc (attr := simp)]
lemma lift_ι {Y : Scheme.{u}} {a b : ι} (f₁ : Y ⟶ (ρ ⁻¹ᵁ U a).toScheme)
    (f₂ : Y ⟶ (ρ ⁻¹ᵁ U b).toScheme) (h : f₁ ≫ (ρ ⁻¹ᵁ U a).ι = f₂ ≫ (ρ ⁻¹ᵁ U b).ι) :
    lift ρ f₁ f₂ h ≫ (U a ⊓ U b).ι = f₁ ≫ (ρ ⁻¹ᵁ U a).ι ≫ ρ :=
  IsOpenImmersion.lift_fac _ _ _

lemma lift_fst {Y : Scheme.{u}} {a b : ι} (f₁ : Y ⟶ (ρ ⁻¹ᵁ U a).toScheme)
    (f₂ : Y ⟶ (ρ ⁻¹ᵁ U b).toScheme) (h : f₁ ≫ (ρ ⁻¹ᵁ U a).ι = f₂ ≫ (ρ ⁻¹ᵁ U b).ι) :
    lift ρ f₁ f₂ h ≫ S.homOfLE (inf_le_left : U a ⊓ U b ≤ U a) = f₁ ≫ ρ ∣_ U a := by
  rw [← cancel_mono (U a).ι]
  simp

lemma lift_snd {Y : Scheme.{u}} {a b : ι} (f₁ : Y ⟶ (ρ ⁻¹ᵁ U a).toScheme)
    (f₂ : Y ⟶ (ρ ⁻¹ᵁ U b).toScheme) (h : f₁ ≫ (ρ ⁻¹ᵁ U a).ι = f₂ ≫ (ρ ⁻¹ᵁ U b).ι) :
    lift ρ f₁ f₂ h ≫ S.homOfLE (inf_le_right : U a ⊓ U b ≤ U b) = f₂ ≫ ρ ∣_ U b := by
  rw [← cancel_mono (U b).ι]
  simp [reassoc_of% h]

lemma comp_lift {Y Y' : Scheme.{u}} {a b : ι} (g : Y' ⟶ Y) (f₁ : Y ⟶ (ρ ⁻¹ᵁ U a).toScheme)
    (f₂ : Y ⟶ (ρ ⁻¹ᵁ U b).toScheme) (h : f₁ ≫ (ρ ⁻¹ᵁ U a).ι = f₂ ≫ (ρ ⁻¹ᵁ U b).ι) :
    g ≫ lift ρ f₁ f₂ h = lift ρ (g ≫ f₁) (g ≫ f₂) (by simp [h]) := by
  rw [← cancel_mono (U a ⊓ U b).ι]
  simp

lemma pullHom_congr {X₁ X₂ : Scheme.{u}} {M₁ : modulesPseudofunctor.obj (.mk (op X₁))}
    {M₂ : modulesPseudofunctor.obj (.mk (op X₂))}
    {Y : Scheme.{u}} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : Scheme.{u}} {g g' : Y' ⟶ Y} (e : g = g') (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom φ g gf₁ gf₂ hgf₁ hgf₂ = pullHom φ g' gf₁ gf₂ (e ▸ hgf₁) (e ▸ hgf₂) := by
  subst e; rfl

/-- The pullback of the gluing morphism `hom a b` to a scheme `Y` with maps `f₁, f₂` to the opens
`ρ⁻¹ U a`, `ρ⁻¹ U b` of `T`. -/
noncomputable def pulledHom ⦃Y : Scheme.{u}⦄ (q : Y ⟶ T) ⦃a b : ι⦄
    (f₁ : Y ⟶ (ρ ⁻¹ᵁ U a).toScheme) (f₂ : Y ⟶ (ρ ⁻¹ᵁ U b).toScheme)
    (hf₁ : f₁ ≫ (ρ ⁻¹ᵁ U a).ι = q) (hf₂ : f₂ ≫ (ρ ⁻¹ᵁ U b).ι = q) :
    (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.obj
        ((modulesPseudofunctor.map (ρ ∣_ U a).op.toLoc).toFunctor.obj (D.obj a)) ⟶
      (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.obj
        ((modulesPseudofunctor.map (ρ ∣_ U b).op.toLoc).toFunctor.obj (D.obj b)) :=
  (modulesPseudofunctor.mapComp' (ρ ∣_ U a).op.toLoc f₁.op.toLoc (f₁ ≫ ρ ∣_ U a).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
      (D.obj a) ≫
    pullHom (D.hom a b) (lift ρ f₁ f₂ (hf₁.trans hf₂.symm)) (f₁ ≫ ρ ∣_ U a) (f₂ ≫ ρ ∣_ U b)
      (lift_fst ρ _ _ _) (lift_snd ρ _ _ _) ≫
    (modulesPseudofunctor.mapComp' (ρ ∣_ U b).op.toLoc f₂.op.toLoc (f₂ ≫ ρ ∣_ U b).op.toLoc
      (by rw [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app
      (D.obj b)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- the kernel check of the final `rw` unfolds the pseudofunctor coherence isomorphisms
/-- The pulled back gluing morphisms are compatible with further pullbacks. -/
lemma pullHom_pulledHom ⦃Y' Y : Scheme.{u}⦄ (g : Y' ⟶ Y) (q : Y ⟶ T) (q' : Y' ⟶ T)
    (hq : g ≫ q = q') ⦃a b : ι⦄ (f₁ : Y ⟶ (ρ ⁻¹ᵁ U a).toScheme)
    (f₂ : Y ⟶ (ρ ⁻¹ᵁ U b).toScheme) (hf₁ : f₁ ≫ (ρ ⁻¹ᵁ U a).ι = q)
    (hf₂ : f₂ ≫ (ρ ⁻¹ᵁ U b).ι = q) (gf₁ : Y' ⟶ (ρ ⁻¹ᵁ U a).toScheme)
    (gf₂ : Y' ⟶ (ρ ⁻¹ᵁ U b).toScheme) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom (D.pulledHom ρ q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂ =
      D.pulledHom ρ q' gf₁ gf₂ (by rw [← hgf₁, Category.assoc, hf₁, hq])
        (by rw [← hgf₂, Category.assoc, hf₂, hq]) := by
  subst hgf₁ hgf₂ hq
  have e := comp_lift ρ g f₁ f₂ (hf₁.trans hf₂.symm)
  dsimp only [pulledHom]
  rw [pullHom_congr (D.hom a b) e.symm _ _ (lift_fst ρ _ _ _) (lift_snd ρ _ _ _),
    ← pullHom_pullHom (D.hom a b) (lift ρ f₁ f₂ (hf₁.trans hf₂.symm)) (f₁ ≫ ρ ∣_ U a)
      (f₂ ≫ ρ ∣_ U b) g ((g ≫ f₁) ≫ ρ ∣_ U a) ((g ≫ f₂) ≫ ρ ∣_ U b) (lift_fst ρ _ _ _)
      (lift_snd ρ _ _ _) (by simp) (by simp)]
  dsimp [pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [modulesPseudofunctor.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ _ _
      (by cat_disch),
    mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ _ _ (by cat_disch)]

end PreDescentData

end AlgebraicGeometry.Scheme.Modules
