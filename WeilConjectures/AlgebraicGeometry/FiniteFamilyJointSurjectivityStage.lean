/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.DescendSurjective
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs

/-!
# Joint surjectivity of a finite family descends to a stage

## References

* Stacks Project, Tag 07RR
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem range_over_pullback {S T : Scheme.{u}} (g : T ⟶ S)
    {U V : Over S} (f : U ⟶ V) :
    Set.range (((Over.pullback g).map f).left) =
      (pullback.fst V.hom g) ⁻¹' Set.range f.left := by
  have heq : (((Over.pullback g).map f).left) =
      pullback.map U.hom g V.hom g f.left (𝟙 T) (𝟙 S)
        (by simp [Over.w f]) (by simp) := by
    apply pullback.hom_ext <;> simp
  rw [heq]
  simpa using (Scheme.Pullback.range_map (f := U.hom) (g := g)
    V.hom g f.left (𝟙 T) (𝟙 S) (by simp [Over.w f]) (by simp))

/-- A finite family of locally finitely presented maps between finite-presentation
models, jointly surjective after pullback to the limit, is jointly surjective at
all sufficiently late stages. This is independent of diagrams, their comparison
isomorphisms, and étaleness of the arrows. (Stacks, Tag 07RR.) -/
theorem finite_family_joint_surjectivity_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (B : Type v) [Finite B] (i : Iᵒᵖ)
    (U : B → Over (D.obj i)) (V : Over (D.obj i))
    (f : ∀ b, U b ⟶ V)
    (hU : ∀ b, LocallyOfFinitePresentation (U b).hom ∧
      QuasiCompact (U b).hom ∧ QuasiSeparated (U b).hom)
    (hV : LocallyOfFinitePresentation V.hom ∧ QuasiCompact V.hom ∧ QuasiSeparated V.hom)
    (hf : ∀ b, LocallyOfFinitePresentation (f b).left)
    (hcov : ∀ x : ((Over.pullback (c.π.app i)).obj V).left,
      ∃ b, ∃ y : ((Over.pullback (c.π.app i)).obj (U b)).left,
        ((Over.pullback (c.π.app i)).map (f b)).left y = x) :
    ∃ (i₁ : Iᵒᵖ) (h₁ : i₁ ⟶ i), ∀ (j : Iᵒᵖ) (h : j ⟶ i₁),
      ∀ x : ((Over.pullback (D.map (h ≫ h₁))).obj V).left,
        ∃ b, ∃ y : ((Over.pullback (D.map (h ≫ h₁))).obj (U b)).left,
          ((Over.pullback (D.map (h ≫ h₁))).map (f b)).left y = x := by
  classical
  let X (b : B) : Scheme.{u} := (U b).left
  let W : Over (D.obj i) := Over.mk (Sigma.desc (fun b ↦ (U b).hom))
  let l (b : B) : U b ⟶ W := Over.homMk (Sigma.ι X b) (by simp [W, X])
  let g : W ⟶ V := Over.homMk (Sigma.desc (fun b ↦ (f b).left)) (by
    apply Sigma.hom_ext
    intro b
    simp [W])
  have hlg (b : B) : l b ≫ g = f b := by ext1; simp [l, g, X]
  have hUX (b : B) : CompactSpace (X b) := by
    have := (hU b).2.1
    exact QuasiCompact.compactSpace_of_compactSpace (U b).hom
  have hUS (b : B) : QuasiSeparatedSpace (X b) := by
    have := (hU b).2.2
    exact quasiSeparatedSpace_of_quasiSeparated (U b).hom
  have hWc : CompactSpace W.left :=
    (finite_coproduct_lfp_qcqs X V.left (fun b ↦ (f b).left)).1 hUX
  have hWs : QuasiSeparatedSpace W.left :=
    (finite_coproduct_lfp_qcqs X V.left (fun b ↦ (f b).left)).2.1 hUS
  have hVc : CompactSpace V.left := by
    have := hV.2.1
    exact QuasiCompact.compactSpace_of_compactSpace V.hom
  have hVs : QuasiSeparatedSpace V.left := by
    have := hV.2.2
    exact quasiSeparatedSpace_of_quasiSeparated V.hom
  have hgp : LocallyOfFinitePresentation g.left :=
    (finite_coproduct_lfp_qcqs X V.left (fun b ↦ (f b).left)).2.2 hf
  have hgc : Surjective (((Over.pullback (c.π.app i)).map g).left) := by
    constructor
    intro x
    obtain ⟨b, y, hy⟩ := hcov x
    refine ⟨(((Over.pullback (c.π.app i)).map (l b)).left) y, ?_⟩
    have H := congrArg (fun k ↦ k.left y)
      (congrArg (fun k ↦ (Over.pullback (c.π.app i)).map k) (hlg b))
    simpa only [Functor.map_comp, Over.comp_left, Scheme.Hom.comp_apply] using H.trans hy
  obtain ⟨i₁, hi₁, hsurj⟩ := exists_surjective_of_isLimit D c hc i.unop W V g hgc
  let h₁ : op i₁ ⟶ i := (homOfLE hi₁).op
  refine ⟨op i₁, h₁, ?_⟩
  intro j h x
  let k := D.map (h ≫ h₁)
  let k₁ := D.map h₁
  let a := D.map h
  have hak : a ≫ k₁ = k := (D.map_comp h h₁).symm
  let z : ↥(pullback V.hom k₁) :=
    pullback.map V.hom k V.hom k₁ (𝟙 _) a (𝟙 _)
      (by simp) (by simpa using hak.symm) x
  have hz : pullback.fst V.hom k₁ z = pullback.fst V.hom k x := by
    change (pullback.map V.hom k V.hom k₁ (𝟙 _) a (𝟙 _)
      (by simp) (by simpa using hak.symm) ≫ pullback.fst V.hom k₁) x = _
    simp
  have hmem : pullback.fst V.hom k x ∈ Set.range g.left := by
    have hzmem : z ∈ Set.range (((Over.pullback k₁).map g).left) := hsurj.surj z
    rw [range_over_pullback] at hzmem
    exact hz ▸ hzmem
  have hxmem : x ∈ Set.range (((Over.pullback k).map g).left) := by
    rw [range_over_pullback]
    exact hmem
  obtain ⟨y, hy⟩ := hxmem
  obtain ⟨b, t, ht⟩ := (sigmaOpenCover X).exists_eq (pullback.fst W.hom k y)
  have hymem : y ∈ Set.range (((Over.pullback k).map (l b)).left) := by
    rw [range_over_pullback]
    exact ⟨t, ht⟩
  obtain ⟨w, hw⟩ := hymem
  refine ⟨b, w, ?_⟩
  have H := congrArg (fun k ↦ k.left w)
    (congrArg (fun f ↦ (Over.pullback k).map f) (hlg b))
  simp only [Functor.map_comp, Over.comp_left, Scheme.Hom.comp_apply, hw] at H
  exact H.symm.trans hy


end AlgebraicGeometry
