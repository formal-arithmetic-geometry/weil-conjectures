/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups B2, J3
-/
module

public import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
import Sheaf.CategoryTheory.DerivedFunctorFixedConeHomColimit
import Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit

/-! # Completion of a derived value triangle

Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause.
-/

@[expose] public section

universe u v uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Functor

/-- Supplied first and second derived maps extend to a distinguished triangle.
Source: Stacks Project, Derived Categories, Lemma 05SC, LF clause.

Proof: Complete lf by TR1. MS2 and the common-stage clause of huX produce a
source denominator square whose retractions commute with lf; the target retraction
stage is kept fixed. The fixed-cone Hom-colimit comparison supplies a third stage
and a map r into the cone K, compatible with its second map. Compose its Hom
bijections with those of the supplied third cone. This proves that precomposition
by p = uZ(sZ) followed by r is bijective on Hom into every W. Surjectivity for
W = LZ gives an inverse, and injectivity for W = K gives its other inverse law.
The second square and hg identify lg followed by p with the second cone map.
Transport the distinguished cone triangle along identities and LZ isomorphic to K,
using p followed by c as the final map.
(blueprint: lem-pur-derived-functor-triangles-05sc-value-triangle-completion) -/
theorem leftDerived_value_triangle_extension_core
    {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [CategoryTheory.IsTriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty C)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    (T : Triangle C) (hT : T ∈ distTriang C)
    (LX LY LZ : D)
    (hX : F.IsTriangulatedLeftDerivedValue S hS T.obj₁ LX)
    (hY : F.IsTriangulatedLeftDerivedValue S hS T.obj₂ LY)
    (hZ : F.IsTriangulatedLeftDerivedValue S hS T.obj₃ LZ)
    (uX : (Functor.const (S.Over ⊤ T.obj₁)).obj LX ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₁ ⋙ Over.forget T.obj₁ ⋙ F)
    (uY : (Functor.const (S.Over ⊤ T.obj₂)).obj LY ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₂ ⋙ Over.forget T.obj₂ ⋙ F)
    (uZ : (Functor.const (S.Over ⊤ T.obj₃)).obj LZ ⟶
      MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F)
    (huX : ∃ s₀ : S.Over ⊤ T.obj₁, ∃ r : F.obj s₀.left ⟶ LX,
      uX.app s₀ ≫ r = 𝟙 LX ∧
        ∀ s : S.Over ⊤ T.obj₁, ∃ t : S.Over ⊤ T.obj₁,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uX.app s)
    (huY : ∃ s₀ : S.Over ⊤ T.obj₂, ∃ r : F.obj s₀.left ⟶ LY,
      uY.app s₀ ≫ r = 𝟙 LY ∧
        ∀ s : S.Over ⊤ T.obj₂, ∃ t : S.Over ⊤ T.obj₂,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uY.app s)
    (huZ : ∃ s₀ : S.Over ⊤ T.obj₃, ∃ r : F.obj s₀.left ⟶ LZ,
      uZ.app s₀ ≫ r = 𝟙 LZ ∧
        ∀ s : S.Over ⊤ T.obj₃, ∃ t : S.Over ⊤ T.obj₃,
          ∃ a : t ⟶ s₀, ∃ b : t ⟶ s,
            F.map b.left = F.map a.left ≫ r ≫ uZ.app s)
    (lf : LX ⟶ LY) (lg : LY ⟶ LZ)
    (hf : ∀ (s : S.Over ⊤ T.obj₁) (s' : S.Over ⊤ T.obj₂)
        (f' : s.left ⟶ s'.left),
        s.hom ≫ T.mor₁ = f' ≫ s'.hom →
          uX.app s ≫ F.map f' = lf ≫ uY.app s')
    (hg : ∀ (s : S.Over ⊤ T.obj₂) (s' : S.Over ⊤ T.obj₃)
        (g' : s.left ⟶ s'.left),
        s.hom ≫ T.mor₂ = g' ≫ s'.hom →
          uY.app s ≫ F.map g' = lg ≫ uZ.app s')
    : ∃ lh : LZ ⟶ (shiftFunctor D (1 : ℤ)).obj LX,
      Triangle.mk lf lg lh ∈ distTriang D := by
  classical
  let : S.HasRightCalculusOfFractions := hS.1.1.2
  have huX' := huX
  have huY' := huY
  obtain ⟨K, b, c, hK⟩ := distinguished_cocone_triangle lf
  obtain ⟨sX₀, rX, hrX, hfacX⟩ := huX'
  obtain ⟨sY₀, rY, hrY, _⟩ := huY'
  obtain ⟨q, hq⟩ :=
    (MorphismProperty.LeftFraction.mk T.mor₁ sY₀.hom sY₀.prop).exists_rightFraction
  let s : S.Over ⊤ T.obj₁ := MorphismProperty.Over.mk ⊤ q.s q.hs
  obtain ⟨t, a, d, hfactor⟩ := hfacX s
  let alpha := F.map a.left ≫ rX
  let f' := d.left ≫ q.f
  have hsq : t.hom ≫ T.mor₁ = f' ≫ sY₀.hom := by
    dsimp only [f']
    rw [Category.assoc, ← hq, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ T.mor₁) (MorphismProperty.Over.w d).symm
  have halpha : uX.app t ≫ alpha = 𝟙 LX := by
    dsimp only [alpha]
    rw [← Category.assoc]
    have hn : uX.app t ≫ F.map a.left = uX.app sX₀ := by
      simpa using (uX.naturality a).symm
    rw [hn, hrX]
  have hret : F.map f' ≫ rY = alpha ≫ lf := by
    have hfq := hf s sY₀ q.f hq
    dsimp only [f', alpha]
    rw [F.map_comp, hfactor]
    simp only [Category.assoc]
    have hm : uX.app s ≫ F.map q.f ≫ rY = lf := by
      rw [← Category.assoc, hfq, Category.assoc, hrY, Category.comp_id]
    exact congrArg (fun k : LX ⟶ LY ↦ F.map a.left ≫ rX ≫ k) hm
  obtain ⟨sZ, g', r, hgsq, hgr, hbij⟩ :=
    leftDerived_fixedCone_homColimit F S hS T hT LX LY hX hY uX uY huX huY
      lf K b c hK t sY₀ f' hsq alpha rY halpha hrY hret
  let G := MorphismProperty.Over.forget S ⊤ T.obj₃ ⋙ Over.forget T.obj₃ ⋙ F
  let p : LZ ⟶ K := uZ.app sZ ≫ r
  have hp (W : D) : Function.Bijective (fun phi : K ⟶ W ↦ p ≫ phi) := by
    obtain ⟨can, hcan, hleg⟩ := essentiallyConstantPro_hom_colimit G LZ hZ uZ huZ W
    have hh := hcan.comp (hbij W)
    have heq : can ∘ (fun phi : K ⟶ W ↦
        (G.op ⋙ yoneda.obj W).ιColimitType (Opposite.op sZ) (r ≫ phi)) =
        (fun phi : K ⟶ W ↦ p ≫ phi) := by
      funext phi
      exact (hleg sZ (r ≫ phi)).trans (Category.assoc _ _ _).symm
    rw [heq] at hh
    exact hh
  obtain ⟨q', hq'⟩ := (hp LZ).surjective (𝟙 LZ)
  change p ≫ q' = 𝟙 LZ at hq'
  have hqp : q' ≫ p = 𝟙 K := by
    apply (hp K).injective
    change p ≫ (q' ≫ p) = p ≫ 𝟙 K
    rw [← Category.assoc, hq', Category.id_comp, Category.comp_id]
  let e : LZ ≅ K := ⟨p, q', hq', hqp⟩
  have hlg : lg ≫ e.hom = b := by
    change lg ≫ (uZ.app sZ ≫ r) = b
    rw [← Category.assoc, ← hg sY₀ sZ g' hgsq, Category.assoc, hgr,
      ← Category.assoc, hrY, Category.id_comp]
  refine ⟨e.hom ≫ c, ?_⟩
  exact isomorphic_distinguished _ hK _
    (Triangle.isoMk _ _ (Iso.refl LX) (Iso.refl LY) e
      (by
        change lf ≫ 𝟙 LY = 𝟙 LX ≫ lf
        rw [Category.comp_id, Category.id_comp])
      (by
        change lg ≫ e.hom = 𝟙 LY ≫ b
        rw [Category.id_comp]
        exact hlg)
      (by
        change (e.hom ≫ c) ≫ (shiftFunctor D (1 : ℤ)).map (𝟙 LX) = e.hom ≫ c
        rw [Functor.map_id, Category.comp_id]))

end CategoryTheory.Functor
