/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitPresentationData
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitRelationVanishing
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-! # Factoring a lifted map through its presentation

Helpers for constructible module Hom descent in Stacks Project, Lemma 09YU (3).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry

private lemma canonical_transition
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (i₀ : I)
    (A : Type (u + 1)) [CommRing A]
    (F G : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A))
    (i j : ConstructibleModuleColimitAbove I i₀) (f : i ⟶ j)
    (a : ConstructibleModuleColimitHomType D i₀ A F G i) :
    ConstructibleModuleColimitCanonicalMap D c i₀ A F G j
        (ConstructibleModuleColimitHomMap D i₀ A F G f a) =
      ConstructibleModuleColimitCanonicalMap D c i₀ A F G i a := by
  let hi := D.map (homOfLE i.property).op
  let hj := D.map (homOfLE j.property).op
  let hij := D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op
  let ti := Etale.upperStar (ModuleCat.{u + 1} A) hi
  let T := Etale.upperStar (ModuleCat.{u + 1} A) hij
  let Li := Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i.val))
  let Lj := Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op j.val))
  have hijc : hj = hij ≫ hi := by dsimp [hj, hij, hi]; rw [← D.map_comp]; rfl
  let e := Etale.upperStarComp (ModuleCat.{u + 1} A) hij hi hj hijc
  let ei := Etale.upperStarComp (ModuleCat.{u + 1} A)
    (c.π.app (op i.val)) hi (c.π.app (op i₀)) (c.w (homOfLE i.property).op).symm
  let ej := Etale.upperStarComp (ModuleCat.{u + 1} A)
    (c.π.app (op j.val)) hj (c.π.app (op i₀)) (c.w (homOfLE j.property).op).symm
  let q := Etale.upperStarComp (ModuleCat.{u + 1} A)
    (c.π.app (op j.val)) hij (c.π.app (op i.val))
    (c.w (homOfLE (show i.val ≤ j.val from leOfHom f)).op).symm
  change ti.obj F ⟶ ti.obj G at a
  have hcoh (H : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A)) :
      ej.hom.app H ≫ Lj.map (e.hom.app H) = ei.hom.app H ≫ q.hom.app (ti.obj H) := by
    simpa [ej, ei, e, q, Lj, ti] using NatTrans.congr_app
      (Etale.upperStarComp_assoc' (ModuleCat.{u + 1} A)
        (c.π.app (op j.val)) hij hi (c.π.app (op i.val)) hj (c.π.app (op i₀))
        (c.w (homOfLE (show i.val ≤ j.val from leOfHom f)).op).symm hijc
        (c.w (homOfLE i.property).op).symm) H
  have hcohi (H : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A)) :
      Lj.map (e.inv.app H) ≫ ej.inv.app H = q.inv.app (ti.obj H) ≫ ei.inv.app H := by
    have he : ej.app H ≪≫ Lj.mapIso (e.app H) = ei.app H ≪≫ q.app (ti.obj H) :=
      Iso.ext (hcoh H)
    exact congrArg Iso.inv he
  change ej.hom.app F ≫ Lj.map (e.hom.app F ≫ T.map a ≫ e.inv.app G) ≫
    ej.inv.app G = ei.hom.app F ≫ Li.map a ≫ ei.inv.app G
  rw [Lj.map_comp, Lj.map_comp]
  calc
    _ = (ej.hom.app F ≫ Lj.map (e.hom.app F)) ≫
        Lj.map (T.map a) ≫ (Lj.map (e.inv.app G) ≫ ej.inv.app G) := by
          simp only [Category.assoc]
    _ = (ei.hom.app F ≫ q.hom.app (ti.obj F)) ≫
        Lj.map (T.map a) ≫ (q.inv.app (ti.obj G) ≫ ei.inv.app G) := by
          rw [hcoh, hcohi]
    _ = _ := by
      have hn : Li.map a ≫ q.hom.app (ti.obj G) =
          q.hom.app (ti.obj F) ≫ Lj.map (T.map a) := q.hom.naturality a
      rw [Category.assoc, ← Category.assoc (q.hom.app _), ← hn]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

/-- A lifted map on the finite free source factors through the descended cokernel after a
later stage when its limit composite is the prescribed map.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), fully faithful paragraph;
(blueprint: lem-weil-pbc-constructible-module-colimit-relation-factor).

Proof: first kill the relation composite at a later stage. The composite inverse-image
functor preserves the presentation cokernel, so its universal property gives a map
between the iterated inverse images. Conjugate by inverse-image composition to obtain
the direct stage map. Associativity of composition makes the canonical Hom comparison
commute with transitions. After precomposition with the pulled-back presentation
epimorphism, its image is the given limit map by the free lift equation. Cancel that
epimorphism. -/
theorem constructibleModuleFinitePresentation_relation_factor
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F₀ G₀ : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF₀ : Scheme.IsConstructibleEtaleModuleSheaf F₀)
    (hG₀ : Scheme.IsConstructibleEtaleModuleSheaf G₀)
    (p : ConstructibleModuleFinitePresentationData A F₀ hF₀)
    (ψ : ((Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))).obj F₀ ⟶
      (Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))).obj G₀))
    (i : I) (h : i₀ ≤ i)
    (a : (Etale.upperStar (ModuleCat.{u + 1} A)
      (D.map (homOfLE h).op)).obj
        (∐ fun k : Fin p.n => p.P (p.U k)) ⟶
      (Etale.upperStar (ModuleCat.{u + 1} A)
        (D.map (homOfLE h).op)).obj G₀)
    (ha : (Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i))).map a ≫
          (Etale.upperStarComp (ModuleCat.{u + 1} A)
            (c.π.app (op i)) (D.map (homOfLE h).op) (c.π.app (op i₀))
            (c.w (homOfLE h).op).symm).inv.app G₀ =
        (Etale.upperStarComp (ModuleCat.{u + 1} A)
          (c.π.app (op i)) (D.map (homOfLE h).op) (c.π.app (op i₀))
          (c.w (homOfLE h).op).symm).inv.app
            (∐ fun k : Fin p.n => p.P (p.U k)) ≫
          (Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))).map p.g ≫ ψ) :
    ∃ (k : ConstructibleModuleColimitAbove I i₀)
      (φ : ConstructibleModuleColimitHomType D i₀ A F₀ G₀ k),
      ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ k φ = ψ := by
  classical
  obtain ⟨k, h', hk⟩ := constructibleModuleFinitePresentation_relation_eventual_zero
    D c hc i₀ A F₀ G₀ hF₀ hG₀ p ψ i h a ha
  let hk₀ : i₀ ≤ k := h.trans h'
  let t := Etale.upperStar (ModuleCat.{u + 1} A) (D.map (homOfLE h).op)
  let T := Etale.upperStar (ModuleCat.{u + 1} A) (D.map (homOfLE h').op)
  let tk := Etale.upperStar (ModuleCat.{u + 1} A) (D.map (homOfLE hk₀).op)
  let e := Etale.upperStarComp (ModuleCat.{u + 1} A)
    (D.map (homOfLE h').op) (D.map (homOfLE h).op)
    (D.map (homOfLE hk₀).op) (by rw [← D.map_comp]; rfl)
  let S := t ⋙ T
  have hkill : S.map p.f ≫ T.map a = 0 := by
    change T.map (t.map p.f) ≫ T.map a = 0
    rw [← T.map_comp]
    exact hk
  let hs := isColimitCoforkMapOfIsColimit' S p.w p.hc.some
  obtain ⟨θ, hθ⟩ := CokernelCofork.IsColimit.desc' hs (T.map a) hkill
  change S.map p.g ≫ θ = T.map a at hθ
  let φ : ConstructibleModuleColimitHomType D i₀ A F₀ G₀ ⟨k, hk₀⟩ :=
    e.hom.app F₀ ≫ θ ≫ e.inv.app G₀
  let j : ConstructibleModuleColimitAbove I i₀ := ⟨k, hk₀⟩
  let ii : ConstructibleModuleColimitAbove I i₀ := ⟨i, h⟩
  let f : ii ⟶ j := homOfLE h'
  let P := ∐ fun l : Fin p.n ↦ p.P (p.U l)
  have hfactor : tk.map p.g ≫ φ =
      ConstructibleModuleColimitHomMap D i₀ A P G₀ f a := by
    change tk.map p.g ≫ (e.hom.app F₀ ≫ θ ≫ e.inv.app G₀) =
      e.hom.app P ≫ T.map a ≫ e.inv.app G₀
    rw [← Category.assoc, e.hom.naturality p.g]
    simp only [Category.assoc]
    rw [← Category.assoc (S.map p.g), hθ]
  let L := Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))
  let Lk := Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op k))
  let E := Etale.upperStarComp (ModuleCat.{u + 1} A)
    (c.π.app (op k)) (D.map (homOfLE hk₀).op) (c.π.app (op i₀))
    (c.w (homOfLE hk₀).op).symm
  have hpre : L.map p.g ≫ ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ j φ =
      ConstructibleModuleColimitCanonicalMap D c i₀ A P G₀ j (tk.map p.g ≫ φ) := by
    change L.map p.g ≫ (E.hom.app F₀ ≫ Lk.map φ ≫ E.inv.app G₀) =
      E.hom.app P ≫ Lk.map (tk.map p.g ≫ φ) ≫ E.inv.app G₀
    have hn : L.map p.g ≫ E.hom.app F₀ =
        E.hom.app P ≫ Lk.map (tk.map p.g) := E.hom.naturality p.g
    calc
      _ = (E.hom.app P ≫ Lk.map (tk.map p.g)) ≫ Lk.map φ ≫ E.inv.app G₀ := by
        rw [← Category.assoc, hn]
      _ = _ := by
        rw [Lk.map_comp (tk.map p.g) φ]
        simp only [Category.assoc]
  let Ei := Etale.upperStarComp (ModuleCat.{u + 1} A)
    (c.π.app (op i)) (D.map (homOfLE h).op) (c.π.app (op i₀))
    (c.w (homOfLE h).op).symm
  have hai : ConstructibleModuleColimitCanonicalMap D c i₀ A P G₀ ii a = L.map p.g ≫ ψ := by
    change Ei.hom.app P ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i))).map a ≫ Ei.inv.app G₀ =
        L.map p.g ≫ ψ
    rw [show (Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i))).map a ≫
        Ei.inv.app G₀ = Ei.inv.app P ≫ L.map p.g ≫ ψ from ha]
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have : Epi p.g := epi_of_isColimit_cofork p.hc.some
  have : Epi (L.map p.g) := inferInstance
  refine ⟨j, φ, (cancel_epi (L.map p.g)).mp ?_⟩
  rw [hpre, hfactor, canonical_transition, hai]

end AlgebraicGeometry
