/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitPresentationData
import WeilConjectures.AlgebraicGeometry.AffineFreeEtaleModuleEventualHomLift
import WeilConjectures.AlgebraicGeometry.FreeEtaleModuleShriekComparison

/-! # Lifting maps from finite affine free generators

Helpers for constructible module Hom descent in Stacks Project, Lemma 09YU (3).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry

/-- A map out of the finite free source of a constructible presentation lifts to a stage.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), fully faithful paragraph;
(blueprint: lem-weil-pbc-constructible-module-colimit-free-lift).

Proof: compare the finite sum of free Yoneda modules with the finite sum of extensions
by zero of the constant rank-one module. Transport the prescribed limit map through
this isomorphism and apply the existing eventual Hom lift. Precompose its stage map
with the pulled-back comparison isomorphism. Naturality of inverse-image composition
and the inverse identities of the comparison give the required equation. -/
theorem constructibleModuleFinitePresentation_free_lift
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F₀ G₀ : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF₀ : Scheme.IsConstructibleEtaleModuleSheaf F₀)
    (_hG₀ : Scheme.IsConstructibleEtaleModuleSheaf G₀)
    (p : ConstructibleModuleFinitePresentationData A F₀ hF₀)
    (ψ : ((Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))).obj F₀ ⟶
      (Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))).obj G₀)) :
    ∃ (i : I) (h : i₀ ≤ i)
      (a : (Etale.upperStar (ModuleCat.{u + 1} A)
        (D.map (homOfLE h).op)).obj
          (∐ fun k : Fin p.n => p.P (p.U k)) ⟶
        (Etale.upperStar (ModuleCat.{u + 1} A)
          (D.map (homOfLE h).op)).obj G₀),
      let e := Etale.upperStarComp (ModuleCat.{u + 1} A)
        (c.π.app (op i)) (D.map (homOfLE h).op) (c.π.app (op i₀))
        (c.w (homOfLE h).op).symm
      (Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i))).map a ≫
          e.inv.app G₀ =
        e.inv.app (∐ fun k : Fin p.n => p.P (p.U k)) ≫
          (Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))).map p.g ≫ ψ := by
  classical
  let Q : (D.obj (op i₀)).Etale →
      Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A) := fun W ↦
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) W.hom inferInstance).obj
      ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        (ModuleCat.of A A))
  let eq (k : Fin p.n) : p.P (p.U k) ≅ Q (p.U k) := by
    simpa [Q, p.P_eq] using
      (Scheme.free_etale_module_shriek_comparison (D.obj (op i₀)) A (p.U k)).some
  let ep : (∐ fun k : Fin p.n => p.P (p.U k)) ≅
      (∐ fun k : Fin p.n => Q (p.U k)) := Sigma.mapIso eq
  let L := Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))
  let fQ := L.map ep.inv ≫ L.map p.g ≫ ψ
  obtain ⟨i, h, aQ, haQ⟩ := Scheme.exists_affine_free_etaleModule_eventual_hom_lift
    D c hc A i₀ p.n (p.U) p.hU G₀ fQ
  let t := Etale.upperStar (ModuleCat.{u + 1} A) (D.map (homOfLE h).op)
  let E := Etale.upperStarComp (ModuleCat.{u + 1} A)
    (c.π.app (op i)) (D.map (homOfLE h).op) (c.π.app (op i₀))
    (c.w (homOfLE h).op).symm
  let a := (t.map ep.hom) ≫ aQ
  refine ⟨i, h, a, ?_⟩
  dsimp [a, fQ] at haQ ⊢
  rw [Functor.map_comp, Category.assoc, haQ]
  have hn := E.inv.naturality ep.hom
  have hn' :
      (Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i))).map
          ((Etale.upperStar (ModuleCat.{u + 1} A) (D.map (homOfLE h).op)).map ep.hom) ≫
        (Etale.upperStarComp (ModuleCat.{u + 1} A)
          (c.π.app (op i)) (D.map (homOfLE h).op) (c.π.app (op i₀))
          (c.w (homOfLE h).op).symm).inv.app (∐ fun k : Fin p.n => Q (p.U k)) =
      (Etale.upperStarComp (ModuleCat.{u + 1} A)
          (c.π.app (op i)) (D.map (homOfLE h).op) (c.π.app (op i₀))
          (c.w (homOfLE h).op).symm).inv.app (∐ fun k : Fin p.n => p.P (p.U k)) ≫
        L.map ep.hom := by simpa [E, Q, p.P_eq, L, t] using hn
  change (Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i))).map
      ((Etale.upperStar (ModuleCat.{u + 1} A) (D.map (homOfLE h).op)).map ep.hom) ≫
      _ = _
  have htarget :
      (Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i))).map
          ((Etale.upperStar (ModuleCat.{u + 1} A) (D.map (homOfLE h).op)).map ep.hom) ≫
        (Etale.upperStarComp (ModuleCat.{u + 1} A)
          (c.π.app (op i)) (D.map (homOfLE h).op) (c.π.app (op i₀))
          (c.w (homOfLE h).op).symm).inv.app
          (∐ fun k : Fin p.n =>
            (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) (p.U k).hom inferInstance).obj
              ((constantSheaf (p.U k).left.smallEtaleTopology
                (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) =
      (Etale.upperStarComp (ModuleCat.{u + 1} A)
          (c.π.app (op i)) (D.map (homOfLE h).op) (c.π.app (op i₀))
          (c.w (homOfLE h).op).symm).inv.app
          (∐ fun k : Fin p.n => p.P (p.U k)) ≫ L.map ep.hom := by
    simpa only [Q] using hn'
  rw [← Category.assoc, htarget]
  have hep : L.map ep.hom ≫ L.map ep.inv = 𝟙 _ := by
    rw [← L.map_comp, ep.hom_inv_id, L.map_id]
  calc
    _ = (Etale.upperStarComp (ModuleCat.{u + 1} A)
          (c.π.app (op i)) (D.map (homOfLE h).op) (c.π.app (op i₀))
          (c.w (homOfLE h).op).symm).inv.app
          (∐ fun k : Fin p.n => p.P (p.U k)) ≫
        (L.map ep.hom ≫ L.map ep.inv) ≫ L.map p.g ≫ ψ := by
          simp only [Category.assoc]
    _ = (Etale.upperStarComp (ModuleCat.{u + 1} A)
          (c.π.app (op i)) (D.map (homOfLE h).op) (c.π.app (op i₀))
          (c.w (homOfLE h).op).symm).inv.app
          (∐ fun k : Fin p.n => p.P (p.U k)) ≫
        (𝟙 _ : L.obj (∐ fun k : Fin p.n => p.P (p.U k)) ⟶ _) ≫
          L.map p.g ≫ ψ := by rw [hep]
    _ = _ := by simp [L]

end AlgebraicGeometry
