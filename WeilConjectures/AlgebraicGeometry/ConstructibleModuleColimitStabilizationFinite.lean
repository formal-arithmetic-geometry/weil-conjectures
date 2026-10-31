/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitHomData
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitStabilizationPairwise
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-! Finite-family common-stage compatibility for constructible module Hom comparison.

The finite-family clause follows from the pairwise clause
`constructibleModuleColimitCanonicalMap_eventually_equal`, directedness of the index and the
composition law of the transition maps on Hom types.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful paragraph
(blueprint: lem-weil-pbc-constructible-module-colimit-stabilization-finite).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry

/-- The transition maps on stage Hom types compose: transporting along `f` and then `g` is
transporting along `f ≫ g`. Both sides conjugate by `Etale.upperStarComp`; they agree by its
associativity (`Etale.map_upperStarComp_hom_app_upperStarComp_inv_app` and
`Etale.upperStarComp_hom_app_map_upperStarComp_inv_app`) and naturality of the composition
isomorphism of the two transitions. -/
private theorem constructibleModuleColimitHomMap_comp
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    (i₀ : I) (A : Type (u + 1)) [CommRing A]
    (F₀ G₀ : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A))
    {i j k : ConstructibleModuleColimitAbove I i₀} (f : i ⟶ j) (g : j ⟶ k)
    (φ : ConstructibleModuleColimitHomType D i₀ A F₀ G₀ i) :
    ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ (f ≫ g) φ =
      ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ g
        (ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ f φ) := by
  let hi := ConstructibleModuleColimitStageMap i₀ D i
  let hj := ConstructibleModuleColimitStageMap i₀ D j
  let hk := ConstructibleModuleColimitStageMap i₀ D k
  let hjk : j.1 ≤ k.1 := g.down.down
  let hij : i.1 ≤ j.1 := f.down.down
  let hik : i.1 ≤ k.1 := (f ≫ g).down.down
  let a := D.map (homOfLE hjk).op
  let b := D.map (homOfLE hij).op
  let ab := D.map (homOfLE hik).op
  have hab : ab = a ≫ b := by
    simp only [ab, a, b, ← D.map_comp]; rfl
  have hj' : hj = b ≫ hi := by
    simp only [hj, b, hi, ConstructibleModuleColimitStageMap, ← D.map_comp]; rfl
  have hk' : hk = ab ≫ hi := by
    simp only [hk, ab, hi, ConstructibleModuleColimitStageMap, ← D.map_comp]; rfl
  have h1 := Etale.map_upperStarComp_hom_app_upperStarComp_inv_app
    (ModuleCat.{u + 1} A) a b hi ab hj hk hab hj' hk' F₀
  have h2 := Etale.upperStarComp_hom_app_map_upperStarComp_inv_app
    (ModuleCat.{u + 1} A) a b hi ab hj hk hab hj' hk' G₀
  let c := Etale.upperStarComp (ModuleCat.{u + 1} A) a b ab hab
  have key : (Etale.upperStar (ModuleCat.{u + 1} A) a).map
      ((Etale.upperStar (ModuleCat.{u + 1} A) b).map φ) =
      c.inv.app _ ≫ (Etale.upperStar (ModuleCat.{u + 1} A) ab).map φ ≫ c.hom.app _ := by
    rw [← NatTrans.naturality_assoc]
    simp
  simp only [ConstructibleModuleColimitHomMap, Functor.map_comp, Category.assoc]
  change _ = _ ≫ (Etale.upperStar (ModuleCat.{u + 1} A) a).map _ ≫
    (Etale.upperStar (ModuleCat.{u + 1} A) a).map
      ((Etale.upperStar (ModuleCat.{u + 1} A) b).map φ) ≫ _
  rw [key]
  simp only [Category.assoc, c]
  rw [reassoc_of% h1, Iso.hom_inv_id_app_assoc, reassoc_of% h2, Iso.hom_inv_id_app,
    Category.comp_id]

/-- Finitely many equalities of canonical Hom representatives hold at one common stage.

Proof. For every pair `(a, b)` with `R a b`, the pairwise clause
`constructibleModuleColimitCanonicalMap_eventually_equal` gives a stage `K (a, b)` above
`i a` and `i b` where the transported representatives agree (for the other pairs take any
common upper bound). The finitely many stages `i₀`, `i a` and `K (a, b)` have a common upper
bound `M` in the directed index; it lies in the tail. Since the tail is thin, the transition
`i a ⟶ M` factors through `K (a, b)`, and the transition maps on Hom types compose
(associativity of `Etale.upperStarComp`), so each equality at `K (a, b)` transports to `M`.
For `n = 0` the bound `M` is any stage above `i₀`.
(blueprint: lem-weil-pbc-constructible-module-colimit-stabilization-finite) -/
theorem constructibleModuleColimitCanonicalMap_eventually_equal_finite
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F₀ G₀ : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF₀ : Scheme.IsConstructibleEtaleModuleSheaf F₀)
    (hG₀ : Scheme.IsConstructibleEtaleModuleSheaf G₀) :
    ∀ (n : ℕ) (i : Fin n → ConstructibleModuleColimitAbove I i₀)
      (φ : ∀ a, ConstructibleModuleColimitHomType D i₀ A F₀ G₀ (i a))
      (R : Fin n → Fin n → Prop),
      (∀ a b, R a b →
        ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ (i a) (φ a) =
          ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ (i b) (φ b)) →
      ∃ (k : ConstructibleModuleColimitAbove I i₀) (f : ∀ a, i a ⟶ k),
        ∀ a b, R a b →
          ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ (f a) (φ a) =
            ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ (f b) (φ b) := by
  intro n i φ R hR
  classical
  have hK : ∀ p : Fin n × Fin n, ∃ (k : ConstructibleModuleColimitAbove I i₀)
      (f : i p.1 ⟶ k) (g : i p.2 ⟶ k), R p.1 p.2 →
        ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ f (φ p.1) =
          ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ g (φ p.2) := by
    intro p
    by_cases h : R p.1 p.2
    · obtain ⟨k, f, g, e⟩ := constructibleModuleColimitCanonicalMap_eventually_equal
        D c hc i₀ A F₀ G₀ hF₀ hG₀ _ _ _ _ (hR _ _ h)
      exact ⟨k, f, g, fun _ => e⟩
    · obtain ⟨k, hk₁, hk₂⟩ := exists_ge_ge (i p.1).1 (i p.2).1
      exact ⟨(⟨k, le_trans (i p.1).2 hk₁⟩ : Set.Ici i₀), ⟨⟨hk₁⟩⟩, ⟨⟨hk₂⟩⟩,
        fun h' => absurd h' h⟩
  choose K fK gK hKe using hK
  obtain ⟨M, hM⟩ := Finite.exists_le (fun x : Option (Fin n ⊕ (Fin n × Fin n)) =>
    match x with
    | none => i₀
    | some (Sum.inl a) => (i a).1
    | some (Sum.inr p) => (K p).1)
  let m : ConstructibleModuleColimitAbove I i₀ := (⟨M, hM none⟩ : Set.Ici i₀)
  refine ⟨m, fun a => ⟨⟨hM (some (Sum.inl a))⟩⟩, ?_⟩
  intro a b hab
  let t : K (a, b) ⟶ m := ⟨⟨hM (some (Sum.inr (a, b)))⟩⟩
  have e := congrArg (ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ t) (hKe (a, b) hab)
  rw [← constructibleModuleColimitHomMap_comp, ← constructibleModuleColimitHomMap_comp] at e
  exact e

end AlgebraicGeometry
