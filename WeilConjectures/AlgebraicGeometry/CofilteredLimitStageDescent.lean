/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Presentable.Directed
public import WeilConjectures.AlgebraicGeometry.DescendSurjective
public import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
public import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descent to a stage of a cofiltered limit of schemes

The descent results `AlgebraicGeometry.Etale.exists_stage_of_inverseLimit` and
`AlgebraicGeometry.exists_eventually_range_subset_of_isConstructible` are stated for inverse
systems indexed by directed preorders. Every cofiltered small category admits an initial functor
from (the opposite of) a directed partial order (`CategoryTheory.IsFiltered.exists_directed`),
which allows us to transfer them to inverse systems indexed by arbitrary cofiltered categories.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I]

/-- A cofiltered small category admits an initial functor from the opposite of a nonempty
directed partial order. -/
lemma IsCofiltered.exists_initial_directed [IsCofiltered I] :
    ∃ (α : Type u) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α)
      (G : αᵒᵖ ⥤ I), G.Initial := by
  obtain ⟨α, _, _, _, F, _⟩ := IsFiltered.exists_directed Iᵒᵖ
  exact ⟨α, _, inferInstance, inferInstance, F.leftOp, inferInstance⟩

variable [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  (c : Cone D) (hc : IsLimit c)

include hc in
/-- If the limit of a cofiltered inverse system of quasi-compact quasi-separated schemes with
affine transition maps maps into a constructible subset `E` of a stage `D i`, then so does
some later stage. -/
theorem exists_range_subset_of_isConstructible_of_isLimit
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] (i : I)
    (E : Set (D.obj i)) (hE : Topology.IsConstructible E)
    (himage : Set.range (c.π.app i) ⊆ E) :
    ∃ (j : I) (h : j ⟶ i), Set.range (D.map h) ⊆ E := by
  obtain ⟨α, _, _, _, G, _⟩ := IsCofiltered.exists_initial_directed (I := I)
  obtain ⟨⟨⟨a⟩, ⟨⟨⟩⟩, g₀⟩⟩ : Nonempty (CostructuredArrow G i) := IsConnected.is_nonempty
  have hc' : IsLimit (c.whisker G) := (Functor.Initial.isLimitWhiskerEquiv G c).symm hc
  have : ∀ {k l : αᵒᵖ} (e : k ⟶ l), IsAffineHom ((G ⋙ D).map e) := fun e ↦
    inferInstanceAs (IsAffineHom (D.map _))
  have : ∀ k : αᵒᵖ, CompactSpace ((G ⋙ D).obj k) := fun k ↦
    inferInstanceAs (CompactSpace (D.obj _))
  have : ∀ k : αᵒᵖ, QuasiSeparatedSpace ((G ⋙ D).obj k) := fun k ↦
    inferInstanceAs (QuasiSeparatedSpace (D.obj _))
  have hE' : Topology.IsConstructible ((D.map g₀) ⁻¹' E) := (D.map g₀).isConstructible_preimage hE
  have himage' : Set.range ((c.whisker G).π.app (op a)) ⊆ (D.map g₀) ⁻¹' E := by
    rintro _ ⟨x, rfl⟩
    change (c.π.app (G.obj (op a)) ≫ D.map g₀) x ∈ E
    rw [c.w]
    exact himage ⟨x, rfl⟩
  obtain ⟨b, hab, hb⟩ := exists_eventually_range_subset_of_isConstructible (G ⋙ D)
    (c.whisker G) hc' a _ hE' himage'
  refine ⟨G.obj (op b), G.map (homOfLE (hab.trans le_rfl)).op ≫ g₀, ?_⟩
  rintro _ ⟨x, rfl⟩
  have := hb b le_rfl ⟨x, rfl⟩
  simpa [Functor.map_comp] using this

include hc in
/-- **Étaleness descends** along a cofiltered inverse system of quasi-compact quasi-separated
schemes with affine transition maps: if `p : X ⟶ D i₀` is of finite presentation and its base
change to the limit is étale, then its base change to some later stage is étale. -/
theorem Etale.exists_stage_of_isLimit (i₀ : I) [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {X : Scheme.{u}} (p : X ⟶ D.obj i₀)
    [LocallyOfFinitePresentation p] [QuasiCompact p] [QuasiSeparated p]
    (hp : Etale (pullback.snd p (c.π.app i₀))) :
    ∃ (j : I) (h : j ⟶ i₀), Etale (pullback.snd p (D.map h)) := by
  obtain ⟨α, _, _, _, G, _⟩ := IsCofiltered.exists_initial_directed (I := I)
  obtain ⟨⟨⟨a⟩, ⟨⟨⟩⟩, g₀⟩⟩ : Nonempty (CostructuredArrow G i₀) := IsConnected.is_nonempty
  have hc' : IsLimit (c.whisker G) := (Functor.Initial.isLimitWhiskerEquiv G c).symm hc
  have : ∀ {k l : αᵒᵖ} (e : k ⟶ l), IsAffineHom ((G ⋙ D).map e) := fun e ↦
    inferInstanceAs (IsAffineHom (D.map _))
  have : ∀ k : αᵒᵖ, CompactSpace ((G ⋙ D).obj k) := fun k ↦
    inferInstanceAs (CompactSpace (D.obj _))
  have : ∀ k : αᵒᵖ, QuasiSeparatedSpace ((G ⋙ D).obj k) := fun k ↦
    inferInstanceAs (QuasiSeparatedSpace (D.obj _))
  let p₁ := pullback.snd p (D.map g₀)
  let X₁ : Over ((G ⋙ D).obj (op a)) := Over.mk p₁
  let Y₁ : Over ((G ⋙ D).obj (op a)) := Over.mk (𝟙 _)
  let f₁ : X₁ ⟶ Y₁ := Over.homMk p₁
  have : CompactSpace X₁.left := QuasiCompact.compactSpace_of_compactSpace p₁
  have : QuasiSeparatedSpace X₁.left := quasiSeparatedSpace_of_quasiSeparated p₁
  have : CompactSpace Y₁.left := inferInstanceAs (CompactSpace (D.obj (G.obj (op a))))
  have : QuasiSeparatedSpace Y₁.left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj (G.obj (op a))))
  have : LocallyOfFinitePresentation f₁.left := inferInstanceAs (LocallyOfFinitePresentation p₁)
  -- the base change of `f₁` along `T ⟶ D (G a)` is, up to isomorphism, `pullback.snd p₁ _`
  have key {T : Scheme.{u}} (g : T ⟶ (G ⋙ D).obj (op a)) :
      Etale ((Over.pullback g).map f₁).left ↔ Etale (pullback.snd p (g ≫ D.map g₀)) := by
    have h₁ : ((Over.pullback g).map f₁).left ≫ pullback.snd (𝟙 _) g = pullback.snd p₁ g := by
      simp [f₁, X₁, Y₁]
    have h₂ : (pullbackLeftPullbackSndIso p (D.map g₀) g).hom ≫ pullback.snd _ _ =
        pullback.snd p₁ g := pullbackLeftPullbackSndIso_hom_snd _ _ _
    rw [← MorphismProperty.cancel_right_of_respectsIso @Etale _ (pullback.snd (𝟙 _) g), h₁,
      ← h₂, MorphismProperty.cancel_left_of_respectsIso @Etale]
  obtain ⟨b, hab, hb⟩ := Etale.exists_stage_of_inverseLimit (G ⋙ D) (c.whisker G) hc' a X₁ Y₁ f₁
    ((key _).2 (by
      have e : (c.whisker G).π.app (op a) ≫ D.map g₀ = c.π.app i₀ := c.w g₀
      rw [e]; exact hp))
  refine ⟨G.obj (op b), G.map (homOfLE hab).op ≫ g₀, ?_⟩
  rw [D.map_comp]
  exact (key _).1 hb

end AlgebraicGeometry
