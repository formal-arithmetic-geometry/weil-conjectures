/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentAux

/-!
# Descent of finite diagrams and isomorphisms to a stage of a cofiltered limit

Let `D : I ⥤ Scheme` be a cofiltered inverse system of quasi-compact quasi-separated schemes with
affine transition maps and limit cone `c`.

* `AlgebraicGeometry.exists_objects_descent`: finitely many qcqs étale `c.pt`-schemes descend to a
  common stage;
* `AlgebraicGeometry.exists_functor_descent`: a functor from a finite category to qcqs étale
  `c.pt`-schemes descends to a stage;
* `AlgebraicGeometry.stageEventually_isIso`: a morphism of qcqs étale schemes over a stage whose
  base change to the limit is an isomorphism is eventually an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D}
  (hc : IsLimit c)

include hc in
/-- Finitely many qcqs étale schemes over the limit descend to a common stage. -/
theorem exists_objects_descent {ι : Type*} [Finite ι] (F : ι → Over c.pt)
    (hF : ∀ a, IsQcqsEtale (F a)) :
    ∃ (i : I) (G : ι → Over (D.obj i)), (∀ a, IsQcqsEtale (G a)) ∧
      Nonempty (∀ a, (Over.pullback (c.π.app i)).obj (G a) ≅ F a) := by
  classical
  choose i₀ U₀ hU₀ e₀ using fun a ↦ exists_isQcqsEtale_overPullback_iso D hc (F a) (hF a)
  have := Fintype.ofFinite ι
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i₀)
  let g : ∀ a, k ⟶ i₀ a := fun a ↦ (hk (Finset.mem_image_of_mem _ (Finset.mem_univ a))).some
  exact ⟨k, fun a ↦ (Over.pullback (D.map (g a))).obj (U₀ a),
    fun a ↦ (hU₀ a).overPullback _,
    ⟨fun a ↦ (overPullbackStageIso D c (g a)).app (U₀ a) ≪≫ (e₀ a).some⟩⟩

include hc in
/-- A functor from a finite category to qcqs étale schemes over the limit descends to a stage. -/
theorem exists_functor_descent {C : Type*} [Category* C] [Finite C]
    [∀ a b : C, Finite (a ⟶ b)] (F : C ⥤ Over c.pt) (hF : ∀ a, IsQcqsEtale (F.obj a)) :
    ∃ (i : I) (G : C ⥤ Over (D.obj i)), (∀ a, IsQcqsEtale (G.obj a)) ∧
      Nonempty (G ⋙ Over.pullback (c.π.app i) ≅ F) := by
  obtain ⟨k, V, hV, ⟨eV⟩⟩ := exists_objects_descent D hc F.obj hF
  -- descend all arrows to a common stage `k₁`
  let ψ : ∀ x : (Σ a b : C, a ⟶ b), (Over.pullback (c.π.app k)).obj (V x.1) ⟶
      (Over.pullback (c.π.app k)).obj (V x.2.1) := fun x ↦
    (eV x.1).hom ≫ F.map x.2.2 ≫ (eV x.2.1).inv
  obtain ⟨k₁, h₁, hh₁⟩ := (StageEventually.finite_forall fun x : (Σ a b : C, a ⟶ b) ↦ by
    obtain ⟨_, _, _, _⟩ := hV x.1
    obtain ⟨_, _, _, _⟩ := hV x.2.1
    exact stageEventually_exists_overPullback_hom D hc (V x.1) (V x.2.1) (ψ x)).exists_hom
  choose φ hφ using hh₁
  let V₁ : C → Over (D.obj k₁) := fun a ↦ (Over.pullback (D.map h₁)).obj (V a)
  have hV₁ : ∀ a, IsQcqsEtale (V₁ a) := fun a ↦ (hV a).overPullback _
  let eV₁ : ∀ a, (Over.pullback (c.π.app k₁)).obj (V₁ a) ≅ F.obj a := fun a ↦
    (overPullbackStageIso D c h₁).app (V a) ≪≫ eV a
  have hφ' : ∀ x : (Σ a b : C, a ⟶ b), (Over.pullback (c.π.app k₁)).map (φ x) ≫
      (eV₁ x.2.1).hom = (eV₁ x.1).hom ≫ F.map x.2.2 := fun x ↦ by
    have := hφ x =≫ (eV x.2.1).hom
    simp only [Category.assoc, ψ, Iso.inv_hom_id, Category.comp_id] at this
    simpa [eV₁] using this
  -- the functoriality relations hold at the limit, hence at a stage `k₂`
  have hid : ∀ a : C, (Over.pullback (c.π.app k₁)).map (φ ⟨a, a, 𝟙 a⟩) =
      (Over.pullback (c.π.app k₁)).map (𝟙 _) := fun a ↦ by
    rw [← cancel_mono (eV₁ a).hom, hφ' ⟨a, a, 𝟙 a⟩]
    simp
  have hcomp : ∀ y : (Σ a b d : C, (a ⟶ b) × (b ⟶ d)),
      (Over.pullback (c.π.app k₁)).map (φ ⟨y.1, y.2.2.1, y.2.2.2.1 ≫ y.2.2.2.2⟩) =
        (Over.pullback (c.π.app k₁)).map (φ ⟨y.1, y.2.1, y.2.2.2.1⟩ ≫
          φ ⟨y.2.1, y.2.2.1, y.2.2.2.2⟩) := fun y ↦ by
    rw [← cancel_mono (eV₁ y.2.2.1).hom, hφ' ⟨y.1, y.2.2.1, _⟩,
      (Over.pullback (c.π.app k₁)).map_comp,
      Category.assoc, hφ' ⟨y.2.1, y.2.2.1, _⟩, reassoc_of% (hφ' ⟨y.1, y.2.1, _⟩), F.map_comp]
  obtain ⟨k₂, g, hg₁, hg₂⟩ := ((StageEventually.finite_forall fun a : C ↦ by
      obtain ⟨_, _, _, _⟩ := hV₁ a
      exact stageEventually_overPullback_map_eq D hc _ _ _ _ (hid a)).and
    (StageEventually.finite_forall fun y : (Σ a b d : C, (a ⟶ b) × (b ⟶ d)) ↦ by
      obtain ⟨_, _, _, _⟩ := hV₁ y.1
      obtain ⟨_, _, _, _⟩ := hV₁ y.2.2.1
      exact stageEventually_overPullback_map_eq D hc _ _ _ _ (hcomp y))).exists_hom
  let G : C ⥤ Over (D.obj k₂) :=
    { obj := fun a ↦ (Over.pullback (D.map g)).obj (V₁ a)
      map := fun {a b} f ↦ (Over.pullback (D.map g)).map (φ ⟨a, b, f⟩)
      map_id := fun a ↦ (hg₁ a).trans ((Over.pullback (D.map g)).map_id _)
      map_comp := fun {a b d} f f' ↦ (hg₂ ⟨a, b, d, f, f'⟩).trans
        ((Over.pullback (D.map g)).map_comp _ _) }
  refine ⟨k₂, G, fun a ↦ (hV₁ a).overPullback _, ⟨NatIso.ofComponents
    (fun a ↦ (overPullbackStageIso D c g).app (V₁ a) ≪≫ eV₁ a) fun {a b} f ↦ ?_⟩⟩
  have n := (overPullbackStageIso D c g).hom.naturality (φ ⟨a, b, f⟩)
  simp only [Functor.comp_map] at n
  simp only [Functor.comp_map, Iso.trans_hom, Iso.app_hom, G]
  rw [reassoc_of% n, hφ' ⟨a, b, f⟩]
  exact (Category.assoc _ _ _).symm

include hc in
/-- A morphism between qcqs étale schemes over a stage whose base change to the limit is an
isomorphism is an isomorphism at all sufficiently late stages. -/
theorem stageEventually_isIso {i : I} {A B : Over (D.obj i)} (hA : IsQcqsEtale A)
    (hB : IsQcqsEtale B) (w : A ⟶ B) [IsIso ((Over.pullback (c.π.app i)).map w)] :
    StageEventually i (fun _ h ↦ IsIso ((Over.pullback (D.map h)).map w)) := by
  obtain ⟨_, _, _, _⟩ := hA
  obtain ⟨_, _, _, _⟩ := hB
  obtain ⟨j₁, h₁, φ, hφ⟩ := (stageEventually_exists_overPullback_hom D hc B A
    (inv ((Over.pullback (c.π.app i)).map w))).exists_hom
  have nw := (overPullbackStageIso D c h₁).hom.naturality w
  simp only [Functor.comp_map] at nw
  have e₁ : (Over.pullback (c.π.app j₁)).map ((Over.pullback (D.map h₁)).map w ≫ φ) =
      (Over.pullback (c.π.app j₁)).map (𝟙 _) := by
    rw [← cancel_mono ((overPullbackStageIso D c h₁).hom.app A),
      Functor.map_comp, Category.assoc, hφ, reassoc_of% nw]
    simp
  have e₂ : (Over.pullback (c.π.app j₁)).map (φ ≫ (Over.pullback (D.map h₁)).map w) =
      (Over.pullback (c.π.app j₁)).map (𝟙 _) := by
    rw [← cancel_mono ((overPullbackStageIso D c h₁).hom.app B),
      Functor.map_comp, Category.assoc, nw, reassoc_of% hφ]
    simp
  have hA₁ := (show IsQcqsEtale A from ⟨‹_›, ‹_›, ‹_›, ‹_›⟩).overPullback (D.map h₁)
  have hB₁ := (show IsQcqsEtale B from ⟨‹_›, ‹_›, ‹_›, ‹_›⟩).overPullback (D.map h₁)
  obtain ⟨_, _, _, _⟩ := hA₁
  obtain ⟨_, _, _, _⟩ := hB₁
  obtain ⟨j₂, g₀, H⟩ := (stageEventually_overPullback_map_eq D hc _ _ _ _ e₁).and
    (stageEventually_overPullback_map_eq D hc _ _ _ _ e₂)
  refine ⟨j₂, g₀ ≫ h₁, fun k g ↦ ?_⟩
  obtain ⟨H₁, H₂⟩ := H g
  rw [(Over.pullback (D.map (g ≫ g₀))).map_comp,
    (Over.pullback (D.map (g ≫ g₀))).map_id] at H₁ H₂
  have : IsIso ((Over.pullback (D.map (g ≫ g₀))).map ((Over.pullback (D.map h₁)).map w)) :=
    ⟨_, H₁, H₂⟩
  rw [← Category.assoc]
  exact (NatIso.isIso_map_iff (overPullbackCompIso D h₁ (g ≫ g₀)) w).mpr this

end AlgebraicGeometry
