/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Spreading out surjective closed immersions from a limit

Let `{Dⱼ}` be a cofiltered system of schemes with Noetherian underlying spaces and affine
transition maps. A surjective closed immersion of finite presentation into `lim Dⱼ` is the base
change of a surjective closed immersion into one of the stages
(`AlgebraicGeometry.exists_isClosedImmersion_surjective_isPullback_of_isLimit`).

Applied to the system of opens `{W_j}` of the base changes `X ×_{D_i} D_j` of a scheme `X` over
a stage, this spreads out a dense open `W` of `X ×_{D_i} lim Dⱼ` together with a surjective
closed immersion `Z ⟶ W` (`AlgebraicGeometry.exists_open_isClosedImmersion_of_isLimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  (hc : IsLimit c) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
/-- If an open `O` of a stage `Dᵢ` of a cofiltered system of schemes with Noetherian
underlying spaces and affine transition maps has empty preimage in the limit, then its preimage
in some later stage is empty. -/
lemma exists_isEmpty_preimage_of_isLimit [∀ i, TopologicalSpace.NoetherianSpace (D.obj i)]
    {i : I} (O : (D.obj i).Opens) (hO : c.π.app i ⁻¹ᵁ O = ⊥) :
    ∃ (j : I) (f : j ⟶ i), D.map f ⁻¹ᵁ O = ⊥ := by
  by_contra! H
  have (j : Over i) : Nonempty ((opensDiagram D i O).obj j) := by
    obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp (H j.left j.hom)
    exact ⟨⟨x, hx⟩⟩
  have (j : Over i) : CompactSpace ((opensDiagram D i O).obj j) :=
    isCompact_iff_compactSpace.mp
      (TopologicalSpace.NoetherianSpace.isCompact (D.map j.hom ⁻¹ᵁ O : Set (D.obj j.left)))
  obtain ⟨⟨x, hx⟩⟩ := Scheme.nonempty_of_isLimit _ _ (isLimitOpensCone D c hc i O)
  rw [hO] at hx
  exact hx

include hc in
/-- **Surjective closed immersions spread out.** Let `{Dⱼ}` be a cofiltered system of schemes
with Noetherian underlying spaces and affine transition maps, `c` a limit cone, and
`z : Z ⟶ lim Dⱼ` a surjective closed immersion of finite presentation. Then `z` is the base
change of a surjective closed immersion `zᵢ : Zᵢ ⟶ Dᵢ` to some stage. -/
theorem exists_isClosedImmersion_surjective_isPullback_of_isLimit
    [∀ i, TopologicalSpace.NoetherianSpace (D.obj i)] {Z : Scheme.{u}} (z : Z ⟶ c.pt)
    [IsClosedImmersion z] [Surjective z] [LocallyOfFinitePresentation z] :
    ∃ (i : I) (Zi : Scheme.{u}) (zi : Zi ⟶ D.obj i) (h : Z ⟶ Zi),
      IsClosedImmersion zi ∧ Surjective zi ∧ IsPullback h z zi (c.π.app i) := by
  obtain ⟨i, Y, p, _, _, _, h, H⟩ := Scheme.exists_isPullback_of_finitePresentation hc z
  obtain ⟨k, f, hf⟩ := Scheme.exists_isClosedImmersion_pullback_snd hc H
  set q := pullback.snd p (D.map f)
  have hq : IsClosedImmersion q := by
    have := hf (𝟙 k)
    rwa [Category.id_comp] at this
  let O : (D.obj k).Opens := ⟨(Set.range q)ᶜ, q.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hO : c.π.app k ⁻¹ᵁ O = ⊥ := by
    refine eq_bot_iff.mpr fun x hx ↦ ?_
    obtain ⟨w, rfl⟩ := z.surjective x
    refine hx ⟨isPullbackLift D c f H w, ?_⟩
    rw [← Scheme.Hom.comp_apply, isPullbackLift_snd]
    rfl
  obtain ⟨j, g, hg⟩ := exists_isEmpty_preimage_of_isLimit hc O hO
  refine ⟨j, pullback p (D.map (g ≫ f)), pullback.snd _ _, isPullbackLift D c (g ≫ f) H,
    hf g, ⟨fun y ↦ ?_⟩, isPullback_isPullbackLift _ H⟩
  have hy : y ∉ D.map g ⁻¹ᵁ O := by simp [hg]
  simp only [Scheme.Hom.mem_preimage, O, TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff,
    not_not, q, Scheme.Pullback.range_snd] at hy
  rw [← Set.mem_range, Scheme.Pullback.range_snd, Set.mem_preimage, Functor.map_comp,
    Scheme.Hom.comp_apply]
  exact hy

/-- An open subscheme of a scheme with Noetherian underlying space has Noetherian underlying
space. -/
instance {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X] (U : X.Opens) :
    TopologicalSpace.NoetherianSpace U.toScheme :=
  inferInstanceAs (TopologicalSpace.NoetherianSpace (U : Set X))

include hc in
/-- **Spreading out an open with a surjective closed immersion.** Let `{Dⱼ}` be a cofiltered
system of Noetherian schemes with affine transition maps, `c` a limit cone, and `p : X ⟶ Dᵢ`
locally of finite type and quasi-compact. Let `W` be a quasi-compact open of
`X_∞ = X ×_{Dᵢ} lim Dⱼ` and `z : Z ⟶ W` a surjective closed immersion of finite presentation.
Then for some `f : j ⟶ i` there are an open `Wⱼ` of `Xⱼ = X ×_{Dᵢ} Dⱼ` with preimage `W` in
`X_∞` and a surjective closed immersion `zⱼ : Zⱼ ⟶ Wⱼ` whose base change along
`lim Dⱼ ⟶ Dⱼ` is `z`. -/
theorem exists_open_isClosedImmersion_of_isLimit [∀ i, IsNoetherian (D.obj i)] {i : I}
    {X : Scheme.{u}} (p : X ⟶ D.obj i) [LocallyOfFiniteType p] [QuasiCompact p]
    (W : (pullback p (c.π.app i)).Opens) (hW : IsCompact (SetLike.coe W))
    {Z : Scheme.{u}} (z : Z ⟶ W.toScheme) [IsClosedImmersion z] [Surjective z]
    [LocallyOfFinitePresentation z] :
    ∃ (j : I) (f : j ⟶ i) (Wj : (pullback p (D.map f)).Opens) (Zj : Scheme.{u})
      (zj : Zj ⟶ Wj.toScheme) (s : Z ⟶ Zj),
      IsClosedImmersion zj ∧ Surjective zj ∧
      pullback.map p (c.π.app i) p (D.map f) (𝟙 X) (c.π.app j) (𝟙 _) (by simp) (by simp) ⁻¹ᵁ
        Wj = W ∧
      IsPullback s (z ≫ W.ι ≫ pullback.snd p (c.π.app i))
        (zj ≫ Wj.ι ≫ pullback.snd p (D.map f)) (c.π.app j) := by
  set BC := baseChangeDiagram D p
  set c' := baseChangeCone D c p
  have hc' : IsLimit c' := isLimitBaseChangeCone D c p hc
  have (j : Over i) : IsNoetherian (BC.obj j) := by
    have : IsLocallyNoetherian (BC.obj j) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p (D.map j.hom))
    have : CompactSpace (BC.obj j) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.snd p (D.map j.hom))
    exact {}
  obtain ⟨j₀, W₀, -, hW₀⟩ := exists_preimage_eq BC c' hc' W hW
  set E := opensDiagram BC j₀ W₀
  set cE := opensCone BC c' j₀ W₀
  have hcE : IsLimit cE := isLimitOpensCone BC c' hc' j₀ W₀
  set z' : Z ⟶ cE.pt := z ≫ ((pullback p (c.π.app i)).isoOfEq hW₀.symm).hom
  have hz' : z' ≫ (c'.π.app j₀ ⁻¹ᵁ W₀).ι = z ≫ W.ι := by simp [z']
  obtain ⟨k, Zk, zk, s, hzk₁, hzk₂, hs⟩ :=
    exists_isClosedImmersion_surjective_isPullback_of_isLimit hcE z'
  have hpre : c'.π.app k.left ⁻¹ᵁ (BC.map k.hom ⁻¹ᵁ W₀) = W := by
    rw [← Scheme.Hom.comp_preimage, c'.w, hW₀]
  refine ⟨k.left.left, k.left.hom, BC.map k.hom ⁻¹ᵁ W₀, Zk, zk, s, hzk₁, hzk₂, hpre, ?_⟩
  have h₂ : IsPullback (cE.π.app k) (c'.π.app j₀ ⁻¹ᵁ W₀).ι (BC.map k.hom ⁻¹ᵁ W₀).ι
      (c'.π.app k.left) := by
    refine IsOpenImmersion.isPullback _ _ _ _ (Scheme.Hom.resLE_comp_ι _ _) ?_
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, ← Scheme.Hom.comp_preimage,
      c'.w]
  have h₃ := isPullback_baseChangeCone_π D c p k.left
  have := (hs.paste_vert h₂).paste_vert h₃
  rw [← hz']
  simpa only [Category.assoc] using this

end

end AlgebraicGeometry
