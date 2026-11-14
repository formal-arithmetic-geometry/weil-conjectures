/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleLimitAcyclicReplacement
import WeilConjectures.AlgebraicGeometry.EtaleLimitCanonicalCohomologyDiagram
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! # Degree reduction for etale limit cohomology

## References

* Stacks Project, Tags 09YQ, 09YP, 09YN and 0739
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
/-- A connecting-map ladder lowers a successor-degree descent problem by one
(Stacks, Tags 09YP and 09YQ). -/
theorem etale_limit_cohomology_connecting_ladder
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L) (n : ℕ)
    (H : I ⥤ AddCommGrpCat.{u + 1})
    (eH : ∀ i : I, H.obj i ≅ AddCommGrpCat.of (Sheaf.H (F i) (n + 1)))
    (hH : ∀ (i j : I) (f : i ⟶ j), H.map f =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (F i) (n + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φ f) (n + 1)) ≫ (eH j).inv)
    (B : Cocone H) (eB : B.pt ≅ AddCommGrpCat.of (Sheaf.H L.pt (n + 1)))
    (hB : ∀ i : I, B.ι.app i ≫ eB.hom =
      (eH i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) (n + 1)) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) (n + 1))) :
    ∃ (FR : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φR : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (FR i) ⟶ FR j)
    (hidentityR : ∀ i : I, φR (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (FR i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (FR i))
    (hcompositionR : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φR (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (FR i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φR f) ≫ φR g)
    (GR : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eGR : ∀ i : I, GR.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (FR i))
    (hGR : ∀ (i j : I) (f : i ⟶ j), GR.map f =
      (eGR i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (FR i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φR f) ≫ (eGR j).inv)
    (LR : Cocone GR) (hLR : IsColimit LR)
    (HR : I ⥤ AddCommGrpCat.{u + 1})
    (eHR : ∀ i : I, HR.obj i ≅ AddCommGrpCat.of (Sheaf.H (FR i) n))
    (hHR : ∀ (i j : I) (f : i ⟶ j), HR.map f =
      (eHR i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (FR i) n) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (φR f) n) ≫ (eHR j).inv)
    (BR : Cocone HR) (eBR : BR.pt ≅ AddCommGrpCat.of (Sheaf.H LR.pt n))
    (hBR : ∀ i : I, BR.ι.app i ≫ eBR.hom =
      (eHR i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (FR i) n) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eGR i).inv ≫ LR.ι.app i) n)),
      ∃ (δ : BR.pt ⟶ B.pt) (δstage : ∀ i : I, HR.obj i ⟶ H.obj i),
        Function.Surjective δ.hom ∧
        (∀ i : I, δstage i ≫ B.ι.app i = BR.ι.app i ≫ δ) := by
  classical
  obtain ⟨FR, φR, hidentityR, hcompositionR, GR, eGR, hGR, LR, hLR,
      E, a, b, w, hE, d, hdformula, hacyclic, beta, hbeta⟩ :=
    etale_limit_acyclic_replacement
      D c hc F φ hidentity hcomposition G eG hG L hL n
  obtain ⟨HR, eHR, hHR, BR, eBR, hBR⟩ :=
    etale_limit_canonical_cohomology_diagram
      D c FR φR hidentityR hcompositionR GR eGR hGR LR n
  have hd : Function.Surjective d.hom := by
    let := hacyclic
    intro x
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hE x
      (Subsingleton.elim _ _) rfl
    exact ⟨y, (hdformula y).trans hy⟩
  let δ : BR.pt ⟶ B.pt := eBR.hom ≫ d ≫ eB.inv
  let δstage (i : I) : HR.obj i ⟶ H.obj i := (eHR i).hom ≫ beta i ≫ (eH i).inv
  refine ⟨FR, φR, hidentityR, hcompositionR, GR, eGR, hGR, LR, hLR,
    HR, eHR, hHR, BR, eBR, hBR, δ, δstage, ?_, ?_⟩
  · have : Epi d := (AddCommGrpCat.epi_iff_surjective d).mpr hd
    exact (AddCommGrpCat.epi_iff_surjective δ).mp (by dsimp [δ]; infer_instance)
  · intro i
    apply (cancel_mono eB.hom).mp
    dsimp [δstage, δ]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hB i]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc (BR.ι.app i), hBR i]
    simpa only [Category.assoc] using congrArg (fun z ↦ (eHR i).hom ≫ z) (hbeta i)


end AlgebraicGeometry.Etale
