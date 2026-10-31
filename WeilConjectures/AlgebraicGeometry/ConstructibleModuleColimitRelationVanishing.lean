/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitPresentationData
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitFullFaithfulStabilization
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekConstantConstructible
import WeilConjectures.AlgebraicGeometry.FreeEtaleModuleShriekComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.ConstructibleSheaf.Monoidal

/-! # Eventual vanishing of presentation relations

Helpers for constructible module Hom descent in Stacks Project, Lemma 09YU (3).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry

/-- Eventual vanishing of a finite affine-free relation after pullback to a later stage.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), section-continuity paragraph;
(blueprint: lem-weil-pbc-constructible-module-colimit-relation-vanishing).

Proof: the relation source is a finite sum of constructible free sheaves: compare its
summands with extension by zero of the constant rank-one module. Its composite with the
lifted map pulls back to zero by naturality and the presentation equation. The zero
clause of the existing stabilization theorem supplies a common later stage. Cancelling
the transition composition isomorphisms gives vanishing under ordinary pullback.
The empty relation sum is included by finite biproduct constructibility.
-/
theorem constructibleModuleFinitePresentation_relation_eventual_zero
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
    ∃ (k : I) (h' : i ≤ k),
      (Etale.upperStar (ModuleCat.{u + 1} A) (D.map (homOfLE h').op)).map
        ((Etale.upperStar (ModuleCat.{u + 1} A) (D.map (homOfLE h).op)).map p.f ≫ a) = 0 := by
  classical
  let R := ∐ fun k : Fin p.m ↦ p.P (p.V k)
  let t := Etale.upperStar (ModuleCat.{u + 1} A) (D.map (homOfLE h).op)
  let L := Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))
  let Li := Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i))
  let E := Etale.upperStarComp (ModuleCat.{u + 1} A)
    (c.π.app (op i)) (D.map (homOfLE h).op) (c.π.app (op i₀))
    (c.w (homOfLE h).op).symm
  have hR : Scheme.IsConstructibleEtaleModuleSheaf R := by
    have hterm (k : Fin p.m) : Scheme.IsConstructibleSheaf (p.P (p.V k)) := by
      have := p.hV k
      let Q := (Etale.etaleLowerShriek (ModuleCat.{u + 1} A)
        (p.V k).hom inferInstance).obj
          ((constantSheaf (p.V k).left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A))
      have hQ := Scheme.isConstructibleEtaleModuleSheaf_etaleLowerShriek_constant
        (X := D.obj (op i₀)) (U := (p.V k).left) (p.V k).hom (ModuleCat.of A A)
      let e : p.P (p.V k) ≅ Q := by
        simpa [p.P_eq, Q] using
          (Scheme.free_etale_module_shriek_comparison (D.obj (op i₀)) A (p.V k)).some
      have := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf Q).mp hQ
      exact Scheme.IsConstructibleSheaf.of_iso e.symm
    have : HasFiniteBiproducts
        (Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
      Abelian.hasFiniteBiproducts
    have := Scheme.IsConstructibleSheaf.biproduct (fun k : Fin p.m ↦ p.P (p.V k))
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf R).mpr
      (Scheme.IsConstructibleSheaf.of_iso (biproduct.isoCoproduct _))
  let b : ConstructibleModuleColimitHomType D i₀ A R G₀ ⟨i, h⟩ := t.map p.f ≫ a
  have hb : ConstructibleModuleColimitCanonicalMap D c i₀ A R G₀ ⟨i, h⟩ b = 0 := by
    change E.hom.app R ≫ Li.map (t.map p.f ≫ a) ≫ E.inv.app G₀ = 0
    have hn : L.map p.f ≫ E.hom.app _ = E.hom.app R ≫ Li.map (t.map p.f) :=
      E.hom.naturality p.f
    calc
      _ = (L.map p.f ≫ E.hom.app _) ≫ Li.map a ≫ E.inv.app G₀ := by
        rw [hn, Li.map_comp]
        simp only [Category.assoc]
      _ = L.map p.f ≫ (E.hom.app _ ≫ (Li.map a ≫ E.inv.app G₀)) := by
        simp only [Category.assoc]
      _ = L.map p.f ≫ (E.hom.app _ ≫ (E.inv.app _ ≫ L.map p.g ≫ ψ)) := by
        rw [show Li.map a ≫ E.inv.app G₀ =
          E.inv.app _ ≫ L.map p.g ≫ ψ from ha]
      _ = L.map p.f ≫ L.map p.g ≫ ψ := by
        simp only [Iso.hom_inv_id_app_assoc]
      _ = L.map (p.f ≫ p.g) ≫ ψ := by
        rw [L.map_comp]
        simp only [Category.assoc]
      _ = 0 := by rw [p.w, L.map_zero, zero_comp]
  obtain ⟨k, f, hf⟩ :=
    (constructibleModuleColimitCanonicalMap_stabilizes D c hc i₀ A R G₀ hR hG₀).2.1
      ⟨i, h⟩ b hb
  refine ⟨k.val, leOfHom f, ?_⟩
  let T := Etale.upperStar (ModuleCat.{u + 1} A)
    (D.map (homOfLE (show i ≤ k.val from leOfHom f)).op)
  let e := Etale.upperStarComp (ModuleCat.{u + 1} A)
    (D.map (homOfLE (show i ≤ k.val from leOfHom f)).op) (D.map (homOfLE h).op)
    (D.map (homOfLE k.property).op) (by rw [← D.map_comp]; rfl)
  change e.hom.app R ≫ T.map b ≫ e.inv.app G₀ = 0 at hf
  have hf' : e.hom.app R ≫ T.map b ≫ e.inv.app G₀ =
      e.hom.app R ≫ 0 ≫ e.inv.app G₀ := by simpa only [comp_zero, zero_comp] using hf
  have hz := (cancel_epi (e.hom.app R)).mp hf'
  have hz' : T.map b = 0 := (cancel_mono (e.inv.app G₀)).mp hz
  simpa only [b, T, t] using hz'

end AlgebraicGeometry
