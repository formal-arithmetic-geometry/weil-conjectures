/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.Data.Fintype.Order
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.CofilteredLimitOverDescent
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Descent of finite étale data to a stage of a cofiltered limit

Let `D` be a cofiltered inverse system of quasi-compact quasi-separated schemes with affine
transition maps and limit cone `c`. We show that quasi-compact quasi-separated étale schemes over
`c.pt`, morphisms and equalities between them, finite diagrams of them (indexed by path categories
of finite quivers, subject to finitely many relations) and finite jointly surjective families
descend to a stage (`AlgebraicGeometry.etale_finite_data_descent`).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A natural transformation between functors out of a path category is natural as soon as it is
natural with respect to the generating arrows. -/
lemma paths_naturality_of_generators {V : Type*} [Quiver V] {C : Type*} [Category* C]
    {F G : Paths V ⥤ C} (app : ∀ a, F.obj a ⟶ G.obj a)
    (h : ∀ ⦃a b : V⦄ (e : a ⟶ b),
      F.map ((Paths.of V).map e) ≫ app b = app a ≫ G.map ((Paths.of V).map e))
    ⦃a b : Paths V⦄ (f : a ⟶ b) : F.map f ≫ app b = app a ≫ G.map f := by
  refine Paths.induction (fun {a b} f ↦ F.map f ≫ app b = app a ≫ G.map f) ?_ ?_ f
  · intro v
    simp
  · intro u v w p q ih
    rw [F.map_comp, G.map_comp, Category.assoc, h, reassoc_of% ih]

/-- A morphism between étale schemes over a base is étale. -/
lemma etale_left_of_etale_hom {S : Scheme.{u}} {U V : Over S} (φ : U ⟶ V) (hU : Etale U.hom)
    (hV : Etale V.hom) : Etale φ.left := by
  have : Etale (φ.left ≫ V.hom) := by rw [Over.w φ]; exact hU
  exact Etale.of_comp φ.left V.hom

section General

variable {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤ Scheme.{u})
  [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D}
  (hc : IsLimit c)

include hc in
/-- Finite diagrams of quasi-compact quasi-separated étale schemes over the limit, indexed by the
path category of a finite quiver and subject to finitely many relations, descend to a stage. -/
theorem exists_paths_functor_descent (A : Type v) [Finite A] [Quiver.{v} A]
    [Finite (Σ a b : A, Quiver.Hom a b)] (R : Type v) [Finite R] (s t : R → Paths A)
    (p q : ∀ r, s r ⟶ t r) (F : Paths A ⥤ Over c.pt) (hF : ∀ a, IsQcqsEtale (F.obj a))
    (hpq : ∀ r, F.map (p r) = F.map (q r)) :
    ∃ (i : J) (G : Paths A ⥤ Over (D.obj i)) (_ : G ⋙ Over.pullback (c.π.app i) ≅ F),
      (∀ a, IsQcqsEtale (G.obj a)) ∧ ∀ r, G.map (p r) = G.map (q r) := by
  classical
  -- descend the objects to a common stage `k`
  choose i₀ U₀ hU₀ e₀ using fun a : A ↦
    exists_isQcqsEtale_overPullback_iso D hc (F.obj a) (hF a)
  have := Fintype.ofFinite A
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i₀)
  let g : ∀ a, k ⟶ i₀ a := fun a ↦ (hk (Finset.mem_image_of_mem _ (Finset.mem_univ a))).some
  let V : A → Over (D.obj k) := fun a ↦ (Over.pullback (D.map (g a))).obj (U₀ a)
  have hV : ∀ a, IsQcqsEtale (V a) := fun a ↦ (hU₀ a).overPullback _
  let eV : ∀ a, (Over.pullback (c.π.app k)).obj (V a) ≅ F.obj a := fun a ↦
    (overPullbackStageIso D c (g a)).app (U₀ a) ≪≫ (e₀ a).some
  -- descend the generating arrows to a common stage `k₁`
  let ψ : ∀ x : (Σ a b : A, Quiver.Hom a b), (Over.pullback (c.π.app k)).obj (V x.1) ⟶
      (Over.pullback (c.π.app k)).obj (V x.2.1) := fun x ↦
    (eV x.1).hom ≫ F.map ((Paths.of A).map x.2.2) ≫ (eV x.2.1).inv
  have hev : StageEventually k (fun _ h ↦ ∀ x : (Σ a b : A, Quiver.Hom a b),
      ∃ φ : (Over.pullback (D.map h)).obj (V x.1) ⟶ (Over.pullback (D.map h)).obj (V x.2.1),
        (Over.pullback (c.π.app _)).map φ ≫ (overPullbackStageIso D c h).hom.app (V x.2.1) =
          (overPullbackStageIso D c h).hom.app (V x.1) ≫ ψ x) :=
    StageEventually.finite_forall fun x ↦ by
      obtain ⟨_, _, _, _⟩ := hV x.1
      obtain ⟨_, _, _, _⟩ := hV x.2.1
      exact stageEventually_exists_overPullback_hom D hc (V x.1) (V x.2.1) (ψ x)
  obtain ⟨k₁, h₁, hh₁⟩ := hev.exists_hom
  choose φ hφ using hh₁
  let G₁ : Paths A ⥤ Over (D.obj k₁) := Paths.lift
    { obj := fun a ↦ (Over.pullback (D.map h₁)).obj (V a)
      map := fun {a b} e ↦ φ ⟨a, b, e⟩ }
  have hG₁ : ∀ a, IsQcqsEtale (G₁.obj a) := fun a ↦ (hV a).overPullback _
  let α₁ : G₁ ⋙ Over.pullback (c.π.app k₁) ≅ F :=
    NatIso.ofComponents (fun a ↦ (overPullbackStageIso D c h₁).app (V a) ≪≫ eV a)
      (fun f ↦ paths_naturality_of_generators _ (fun a b e ↦ by
        have := hφ ⟨a, b, e⟩
        simp only [Functor.comp_map, G₁, Paths.lift_toPath, Iso.trans_hom, Iso.app_hom]
        rw [reassoc_of% this]
        simp [ψ]) f)
  -- descend the relations to a stage `k₂`
  have hrel : ∀ r, (Over.pullback (c.π.app k₁)).map (G₁.map (p r)) =
      (Over.pullback (c.π.app k₁)).map (G₁.map (q r)) := fun r ↦ by
    have h1 := NatIso.naturality_2 α₁ (p r)
    have h2 := NatIso.naturality_2 α₁ (q r)
    simp only [Functor.comp_map] at h1 h2
    rw [← h1, ← h2, hpq r]
  have hev₂ : StageEventually k₁ (fun _ h ↦ ∀ r : R,
      (Over.pullback (D.map h)).map (G₁.map (p r)) =
        (Over.pullback (D.map h)).map (G₁.map (q r))) :=
    StageEventually.finite_forall fun r ↦ by
      obtain ⟨_, _, _, _⟩ := hG₁ (s r)
      obtain ⟨_, _, _, _⟩ := hG₁ (t r)
      exact stageEventually_overPullback_map_eq D hc _ _ _ _ (hrel r)
  obtain ⟨k₂, h₂, hh₂⟩ := hev₂.exists_hom
  exact ⟨k₂, G₁ ⋙ Over.pullback (D.map h₂),
    Functor.isoWhiskerLeft G₁ (overPullbackStageIso D c h₂) ≪≫ α₁,
    fun a ↦ (hG₁ a).overPullback _, hh₂⟩

include hc in
/-- A finite family of morphisms between quasi-compact quasi-separated étale schemes over a stage
whose base change to the limit is jointly surjective is jointly surjective at all sufficiently
late stages. -/
theorem exists_stage_jointly_surjective {i : J} {ι : Type*} (B : Finset ι) (X : Over (D.obj i))
    (Y : ι → Over (D.obj i)) (f : ∀ e, Y e ⟶ X) (hX : IsQcqsEtale X)
    (hY : ∀ e, IsQcqsEtale (Y e))
    (hsurj : ∀ x : ((Over.pullback (c.π.app i)).obj X).left, ∃ e ∈ B,
      ∃ y : ((Over.pullback (c.π.app i)).obj (Y e)).left,
        ((Over.pullback (c.π.app i)).map (f e)).left y = x) :
    ∃ (i₁ : J) (h₁ : i₁ ⟶ i), ∀ (j : J) (h : j ⟶ i₁)
      (x : ((Over.pullback (D.map (h ≫ h₁))).obj X).left), ∃ e ∈ B,
        ∃ y : ((Over.pullback (D.map (h ≫ h₁))).obj (Y e)).left,
          ((Over.pullback (D.map (h ≫ h₁))).map (f e)).left y = x := by
  classical
  obtain ⟨hXe, _, _, _⟩ := hX
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  let E : Set X.left := ⋃ e : B, Set.range (f e).left
  have hE : Topology.IsConstructible E := by
    refine Topology.IsConstructible.iUnion fun e ↦ ?_
    obtain ⟨hYe, _, _, _⟩ := hY e
    have : CompactSpace (Y e).left := QuasiCompact.compactSpace_of_compactSpace (Y e).hom
    have : Etale (f e).left := etale_left_of_etale_hom (f e) hYe hXe
    simpa using (f e).left.isConstructible_image Topology.IsConstructible.univ
  -- the image of the limit lies in `E`
  have himage : Set.range ((baseChangeCone D c X.hom).π.app (Over.mk (𝟙 i))) ⊆
      (pullback.fst X.hom (D.map (𝟙 i))) ⁻¹' E := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨e, he, y, hy⟩ := hsurj x
    refine Set.mem_iUnion.mpr ⟨⟨e, he⟩, pullback.fst (Y e).hom (c.π.app i) y, ?_⟩
    have h1 := congrArg (fun φ ↦ φ x) (baseChangeCone_π_app_fst D c X.hom (Over.mk (𝟙 i)))
    have h2 := congrArg (fun φ ↦ φ y) (pullback.lift_fst
      (pullback.fst (Y e).hom (c.π.app i) ≫ (f e).left) (pullback.snd (Y e).hom (c.π.app i))
      (by simp [pullback.condition]))
    simp only [Scheme.Hom.comp_apply] at h1 h2
    simp only [Set.mem_preimage, h1]
    rw [← hy]
    exact h2.symm
  obtain ⟨k, m, hk⟩ := exists_range_subset_of_isConstructible_of_isLimit
    (baseChangeDiagram D X.hom) (baseChangeCone D c X.hom) (isLimitBaseChangeCone D c X.hom hc)
    (Over.mk (𝟙 i)) _ ((pullback.fst X.hom (D.map (𝟙 i))).isConstructible_preimage hE) himage
  have hstage : ∀ z : pullback X.hom (D.map k.hom), pullback.fst X.hom (D.map k.hom) z ∈ E := by
    intro z
    have h1 := congrArg (fun φ ↦ φ z) (baseChangeDiagram_map_fst D X.hom m)
    simp only [Scheme.Hom.comp_apply] at h1
    have := hk ⟨z, rfl⟩
    simp only [Set.mem_preimage, h1] at this
    exact this
  refine ⟨k.left, k.hom, fun j h x ↦ ?_⟩
  set g := D.map (h ≫ k.hom) with hg
  have hx : pullback.fst X.hom g x ∈ E := by
    let z := pullback.map X.hom g X.hom (D.map k.hom) (𝟙 _) (D.map h) (𝟙 _) (by simp)
      (by simp [hg])
    have h1 := congrArg (fun φ ↦ φ x) (pullback.lift_fst (pullback.fst X.hom g ≫ 𝟙 _)
      (pullback.snd X.hom g ≫ D.map h) (by simp [hg, pullback.condition]))
    simp only [Scheme.Hom.comp_apply, Category.comp_id] at h1
    have := hstage z
    rw [show pullback.fst X.hom (D.map k.hom) z = pullback.fst X.hom g x from h1] at this
    exact this
  obtain ⟨⟨e, he⟩, z, hz⟩ := Set.mem_iUnion.mp hx
  have hs : IsPullback (((Over.pullback g).map (f e)).left ≫ pullback.snd X.hom g)
      (pullback.fst (Y e).hom g) g ((f e).left ≫ X.hom) := by
    have e1 : ((Over.pullback g).map (f e)).left ≫ pullback.snd X.hom g =
        pullback.snd (Y e).hom g := by simp
    rw [e1, Over.w (f e)]
    exact (IsPullback.of_hasPullback (Y e).hom g).flip
  have houter : IsPullback ((Over.pullback g).map (f e)).left (pullback.fst (Y e).hom g)
      (pullback.fst X.hom g) (f e).left :=
    IsPullback.of_right hs (by simp) (IsPullback.of_hasPullback X.hom g).flip
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback houter x z hz.symm
  exact ⟨e, he, y, hy⟩

end General

/-- Blueprint `lem-weil-pbc-etale-finite-data-descent`: quasi-compact quasi-separated étale
schemes, morphisms, equalities, finite diagrams and finite jointly surjective families over the
limit of a directed inverse system of qcqs schemes with affine transition maps descend to a
stage. -/
theorem etale_finite_data_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    (∀ U : Over c.pt,
      (Etale U.hom ∧ LocallyOfFinitePresentation U.hom ∧
        QuasiCompact U.hom ∧ QuasiSeparated U.hom) →
      ∃ (i : Iᵒᵖ) (Ui : Over (D.obj i)),
        (Etale Ui.hom ∧ LocallyOfFinitePresentation Ui.hom ∧
          QuasiCompact Ui.hom ∧ QuasiSeparated Ui.hom) ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Ui ≅ U)) ∧
    (∀ (i : Iᵒᵖ) (U V : Over (D.obj i)),
      (Etale U.hom ∧ LocallyOfFinitePresentation U.hom ∧
        QuasiCompact U.hom ∧ QuasiSeparated U.hom) →
      (Etale V.hom ∧ LocallyOfFinitePresentation V.hom ∧
        QuasiCompact V.hom ∧ QuasiSeparated V.hom) →
      ∀ ψ : (Over.pullback (c.π.app i)).obj U ⟶ (Over.pullback (c.π.app i)).obj V,
        ∃ (j : Iᵒᵖ) (h : j ⟶ i)
          (ψj : (Over.pullback (D.map h)).obj U ⟶ (Over.pullback (D.map h)).obj V),
          (Over.pullback (c.π.app j)).map ψj ≫
              (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))).app
                  V).hom =
            (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))).app
                  U).hom ≫ ψ) ∧
    (∀ (i : Iᵒᵖ) (U V : Over (D.obj i)),
      (Etale U.hom ∧ LocallyOfFinitePresentation U.hom ∧
        QuasiCompact U.hom ∧ QuasiSeparated U.hom) →
      (Etale V.hom ∧ LocallyOfFinitePresentation V.hom ∧
        QuasiCompact V.hom ∧ QuasiSeparated V.hom) →
      ∀ ψ χ : U ⟶ V, (Over.pullback (c.π.app i)).map ψ = (Over.pullback (c.π.app i)).map χ →
        ∃ (j : Iᵒᵖ) (h : j ⟶ i),
          (Over.pullback (D.map h)).map ψ = (Over.pullback (D.map h)).map χ) ∧
    (∀ (A : Type v) [Finite A] [Quiver.{v} A]
      [Finite (Σ a b : A, Quiver.Hom a b)]
      (R : Type v) [Finite R] (s t : R → Paths A)
      (p q : ∀ r, s r ⟶ t r) (F : Paths A ⥤ Over c.pt),
      (∀ a, Etale (F.obj a).hom ∧ LocallyOfFinitePresentation (F.obj a).hom ∧
        QuasiCompact (F.obj a).hom ∧ QuasiSeparated (F.obj a).hom) →
      (∀ r, F.map (p r) = F.map (q r)) →
        ∃ (i : Iᵒᵖ) (G : Paths A ⥤ Over (D.obj i)) (α : G ⋙ Over.pullback (c.π.app i) ≅ F),
          (∀ a, Etale (G.obj a).hom ∧ LocallyOfFinitePresentation (G.obj a).hom ∧
            QuasiCompact (G.obj a).hom ∧ QuasiSeparated (G.obj a).hom) ∧
          (∀ r, G.map (p r) = G.map (q r)) ∧
          ∀ (j : Iᵒᵖ) (h : j ⟶ i),
            (∀ a, Etale ((G ⋙ Over.pullback (D.map h)).obj a).hom ∧
              LocallyOfFinitePresentation ((G ⋙ Over.pullback (D.map h)).obj a).hom ∧
              QuasiCompact ((G ⋙ Over.pullback (D.map h)).obj a).hom ∧
              QuasiSeparated ((G ⋙ Over.pullback (D.map h)).obj a).hom) ∧
            (∀ r, (G ⋙ Over.pullback (D.map h)).map (p r) =
              (G ⋙ Over.pullback (D.map h)).map (q r)) ∧
            ∀ (a b : Paths A) (f : a ⟶ b),
              ((G ⋙ Over.pullback (D.map h)) ⋙ Over.pullback (c.π.app j)).map f ≫
                  (Functor.isoWhiskerLeft G ((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))) ≪≫
                      α).hom.app b =
                (Functor.isoWhiskerLeft G ((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))) ≪≫
                      α).hom.app a ≫ F.map f) ∧
    (∀ (A : Type v) [Finite A] [Quiver.{v} A]
      [Finite (Σ a b : A, Quiver.Hom a b)]
      (i : Iᵒᵖ) (G : Paths A ⥤ Over (D.obj i)) (F : Paths A ⥤ Over c.pt)
      (α : G ⋙ Over.pullback (c.π.app i) ≅ F),
      (∀ a, Etale (G.obj a).hom ∧ LocallyOfFinitePresentation (G.obj a).hom ∧
        QuasiCompact (G.obj a).hom ∧ QuasiSeparated (G.obj a).hom) →
      ∀ (b : A) (B : Finset (Σ a : A, Quiver.Hom a b)),
        (∀ x : (F.obj b).left, ∃ e ∈ B, ∃ y : (F.obj e.1).left,
          (F.map ((Paths.of A).map e.2)).left y = x) →
        ∃ (i₁ : Iᵒᵖ) (h₁ : i₁ ⟶ i), ∀ (j : Iᵒᵖ) (h : j ⟶ i₁),
          (∀ e ∈ B,
            Etale (((G ⋙ Over.pullback (D.map (h ≫ h₁))).map ((Paths.of A).map e.2)).left)) ∧
          (∀ x : ((G ⋙ Over.pullback (D.map (h ≫ h₁))).obj b).left,
            ∃ e ∈ B, ∃ y : ((G ⋙ Over.pullback (D.map (h ≫ h₁))).obj e.1).left,
              ((G ⋙ Over.pullback (D.map (h ≫ h₁))).map ((Paths.of A).map e.2)).left y = x)) := by
  refine ⟨fun U hU ↦ exists_isQcqsEtale_overPullback_iso D hc U hU, ?_, ?_, ?_, ?_⟩
  · intro i U V hU hV ψ
    obtain ⟨_, _, _, _⟩ := hU
    obtain ⟨_, _, _, _⟩ := hV
    obtain ⟨j, h, φ, hφ⟩ := (stageEventually_exists_overPullback_hom D hc U V ψ).exists_hom
    exact ⟨j, h, φ, hφ⟩
  · intro i U V hU hV ψ χ hψχ
    obtain ⟨_, _, _, _⟩ := hU
    obtain ⟨_, _, _, _⟩ := hV
    exact (stageEventually_overPullback_map_eq D hc U V ψ χ hψχ).exists_hom
  · intro A _ _ _ R _ s t p q F hF hpq
    obtain ⟨i, G, α, hG, hrel⟩ := exists_paths_functor_descent D hc A R s t p q F hF hpq
    refine ⟨i, G, α, hG, hrel, fun j h ↦ ⟨fun a ↦ (hG a).overPullback _,
      fun r ↦ by simp only [Functor.comp_map, hrel r], fun a b f ↦ ?_⟩⟩
    exact (Functor.isoWhiskerLeft G (overPullbackStageIso D c h) ≪≫ α).hom.naturality f
  · intro A _ _ _ i G F α hG b B hsurj
    have hsurj' : ∀ x : ((Over.pullback (c.π.app i)).obj (G.obj b)).left, ∃ e ∈ B,
        ∃ y : ((Over.pullback (c.π.app i)).obj (G.obj e.1)).left,
          ((Over.pullback (c.π.app i)).map (G.map ((Paths.of A).map e.2))).left y = x := by
      intro x
      obtain ⟨e, he, y, hy⟩ := hsurj ((α.hom.app b).left x)
      refine ⟨e, he, (α.inv.app e.1).left y, ?_⟩
      have hn := NatIso.naturality_1 α ((Paths.of A).map e.2)
      simp only [Functor.comp_map] at hn
      rw [← hn]
      simp only [Over.comp_left, Scheme.Hom.comp_apply]
      have h1 := Scheme.inv_hom_apply ((Over.forget _).mapIso (α.app e.1)) y
      have h2 := Scheme.hom_inv_apply ((Over.forget _).mapIso (α.app b)) x
      simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
        Over.forget_map] at h1 h2
      rw [h1, hy, h2]
    obtain ⟨i₁, h₁, H⟩ := exists_stage_jointly_surjective D hc B (G.obj b)
      (fun e ↦ G.obj e.1) (fun e ↦ G.map ((Paths.of A).map e.2)) (hG b) (fun e ↦ hG e.1) hsurj'
    refine ⟨i₁, h₁, fun j h ↦ ⟨fun e _ ↦ ?_, H j h⟩⟩
    exact etale_left_of_etale_hom _ ((hG e.1).overPullback _).1 ((hG b).overPullback _).1

end AlgebraicGeometry
