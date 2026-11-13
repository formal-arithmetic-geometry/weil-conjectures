/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleLimitCompatibleExactSystems
import WeilConjectures.AlgebraicGeometry.EtaleLimitCanonicalCohomologyDiagram

/-! # Exact connecting ladders for affine-stage cohomology

Source: Stacks Project, Tags 09YQ, 09YP, 09YN and 0739.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem cohomologyMap_boundary {X Y : Scheme.{u}} (f : Y ⟶ X)
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact) (n : ℕ) (z : Sheaf.H S.X₃ n) :
    cohomologyMap f S.X₁ (n + 1) (Sheaf.H.δSucc hS n z) =
      Sheaf.H.δSucc (hS.map_of_exact (upperStar AddCommGrpCat.{u + 1} f)) n
        (cohomologyMap f S.X₃ n z) := by
  change cohomologyMap f S.X₁ (n + 1) (z.comp hS.extClass rfl) =
    (cohomologyMap f S.X₃ n z).comp
      (hS.map_of_exact (upperStar AddCommGrpCat.{u + 1} f)).extClass rfl
  rw [cohomologyMap_apply, cohomologyMap_apply,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_extClass]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

private theorem cohomology_boundary_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact)
    (S' : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS' : S'.ShortExact)
    (t : S.map (upperStar AddCommGrpCat.{u + 1} f) ⟶ S')
    (n : ℕ) (z : Sheaf.H S.X₃ n) :
    Sheaf.H.map t.τ₁ (n + 1)
        (cohomologyMap f S.X₁ (n + 1) (Sheaf.H.δSucc hS n z)) =
      Sheaf.H.δSucc hS' n
        (Sheaf.H.map t.τ₃ n (cohomologyMap f S.X₃ n z)) := by
  exact (congrArg (Sheaf.H.map t.τ₁ (n + 1))
    (cohomologyMap_boundary f S hS n z)).trans
      (Sheaf.H.map_δSucc
        (hS.map_of_exact (upperStar AddCommGrpCat.{u + 1} f)) hS' t n _)

private theorem cohomology_middle_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (S' : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (t : S.map (upperStar AddCommGrpCat.{u + 1} f) ⟶ S')
    (n : ℕ) (z : Sheaf.H S.X₂ n) :
    Sheaf.H.map t.τ₃ n (cohomologyMap f S.X₃ n (Sheaf.H.map S.g n z)) =
      Sheaf.H.map S'.g n (Sheaf.H.map t.τ₂ n (cohomologyMap f S.X₂ n z)) := by
  rw [cohomologyMap_map f n S.g z]
  exact (Sheaf.H.map_comp_apply
    ((upperStar AddCommGrpCat.{u + 1} f).map S.g) t.τ₃ _).symm.trans
      ((congrArg (fun h ↦ Sheaf.H.map h n (cohomologyMap f S.X₂ n z))
        t.comm₂₃.symm).trans (Sheaf.H.map_comp_apply t.τ₂ S'.g _))

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- Exact connecting rows and their comparison squares for an affine-stage system
(Stacks, Tags 09YP, 0EXZ, 0739, 0EYL and 04HR). -/
theorem etale_limit_affine_exact_ladder
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, IsAffine (D.obj i)]
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
    (L : Cocone G) (hL : IsColimit L)
    (n : ℕ) (result : Prop)
    (continuation : ∀ (E : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (ψ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (E i) ⟶ E j)
    (hidE : ∀ i : I, ψ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (E i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (E i))
    (hcompE : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      ψ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (E i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (ψ f) ≫ ψ g)
    (GE : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eGE : ∀ i : I, GE.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (E i))
    (hGE : ∀ (i j : I) (f : i ⟶ j), GE.map f =
      (eGE i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (E i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (ψ f) ≫ (eGE j).inv)
    (LE : Cocone GE) (hLE : IsColimit LE)
    (HE : I ⥤ AddCommGrpCat.{u + 1})
    (eHE : ∀ i : I, HE.obj i ≅ AddCommGrpCat.of (Sheaf.H (E i) n))
    (hHE : ∀ (i j : I) (f : i ⟶ j), HE.map f =
      (eHE i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (D.map f.op) (E i) n) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map (ψ f) n) ≫ (eHE j).inv)
    (BE : Cocone HE) (eBE : BE.pt ≅ AddCommGrpCat.of (Sheaf.H LE.pt n))
    (hBE : ∀ i : I, BE.ι.app i ≫ eBE.hom =
      (eHE i).hom ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (E i) n) ≫
        AddCommGrpCat.ofHom (Sheaf.H.map ((eGE i).inv ≫ LE.ι.app i) n))
    (R : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (ρ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (R i) ⟶ R j)
    (hidentityR : ∀ i : I, ρ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (R i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (R i))
    (hcompositionR : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      ρ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (R i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (ρ f) ≫ ρ g)
    (T : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eT : ∀ i : I, T.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (R i))
    (hT : ∀ (i j : I) (f : i ⟶ j), T.map f =
      (eT i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (R i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (ρ f) ≫ (eT j).inv)
    (K : Cocone T) (hK : IsColimit K)
    (δ : ∀ k : I, Sheaf.H (R k) n →+ Sheaf.H (F k) (n + 1))
    (α : ∀ k : I, HE.obj k →+ Sheaf.H (R k) n)
    (α₀ : BE.pt →+ Sheaf.H K.pt n)
    (β : Sheaf.H K.pt n →+ Sheaf.H L.pt (n + 1)),
      (∀ k : I, Function.Surjective (δ k)) ∧
      (∀ (k : I) (v : HE.obj k), δ k (α k v) = 0) ∧
      (∀ (j k : I) (g : j ⟶ k) (z : Sheaf.H (R j) n),
        δ k (Sheaf.H.map (ρ g) n (cohomologyMap (D.map g.op) (R j) n z)) =
          Sheaf.H.map (φ g) (n + 1)
            (cohomologyMap (D.map g.op) (F j) (n + 1) (δ j z))) ∧
      (∀ (k : I) (z : Sheaf.H (R k) n),
        β (Sheaf.H.map ((eT k).inv ≫ K.ι.app k) n
          (cohomologyMap (c.π.app (op k)) (R k) n z)) =
        Sheaf.H.map ((eG k).inv ≫ L.ι.app k) (n + 1)
          (cohomologyMap (c.π.app (op k)) (F k) (n + 1) (δ k z))) ∧
      (∀ (k : I) (v : HE.obj k),
        Sheaf.H.map ((eT k).inv ≫ K.ι.app k) n
          (cohomologyMap (c.π.app (op k)) (R k) n (α k v)) =
        α₀ ((BE.ι.app k).hom v)) ∧
      (∀ y : Sheaf.H K.pt n, β y = 0 → ∃ w : BE.pt, α₀ w = y) ∧
      (∀ (j k : I) (g : j ⟶ k) (z : Sheaf.H (R j) n),
        Sheaf.H.map ((eT k).inv ≫ K.ι.app k) n
          (cohomologyMap (c.π.app (op k)) (R k) n
            (Sheaf.H.map (ρ g) n (cohomologyMap (D.map g.op) (R j) n z))) =
        Sheaf.H.map ((eT j).inv ≫ K.ι.app j) n
          (cohomologyMap (c.π.app (op j)) (R j) n z)) → result) : result := by
  classical
  apply etale_limit_compatible_exact_systems
    D c F φ hidentity hcomposition G eG hG L hL result
  intro R ρ hidentityR hcompositionR T eT hT K hK
    E ψ hidE hcompE GE eGE hGE LE hLE a b w hS ai bi wi hi t r hcompat
  obtain ⟨hr₁, hr₂, hr₃, ht₂, hinj, ht₁, ht₃⟩ := hcompat
  obtain ⟨HE, eHE, hHE, BE, eBE, hBE⟩ :=
    etale_limit_canonical_cohomology_diagram D c E ψ hidE hcompE GE eGE hGE LE n
  obtain ⟨HR, eHR, hHR, BR, eBR, hBR⟩ :=
    etale_limit_canonical_cohomology_diagram
      D c R ρ hidentityR hcompositionR T eT hT K n
  have hlegs (j k : I) (g : j ⟶ k) (z : Sheaf.H (R j) n) :
      Sheaf.H.map ((eT k).inv ≫ K.ι.app k) n
          (cohomologyMap (c.π.app (op k)) (R k) n
            (Sheaf.H.map (ρ g) n (cohomologyMap (D.map g.op) (R j) n z))) =
        Sheaf.H.map ((eT j).inv ≫ K.ι.app j) n
          (cohomologyMap (c.π.app (op j)) (R j) n z) := by
    have hcat : HR.map g ≫ BR.ι.app k ≫ eBR.hom = BR.ι.app j ≫ eBR.hom := by
      rw [← Category.assoc, BR.w g]
    rw [hBR k, hBR j, hHR j k g] at hcat
    simp only [Category.assoc, Iso.inv_hom_id_assoc] at hcat
    have hh := (cancel_epi (eHR j).hom).1 hcat
    exact congrArg (fun f ↦ f.hom z) hh
  let δ (i : I) : Sheaf.H (R i) n →+ Sheaf.H (F i) (n + 1) :=
    Sheaf.H.δSucc (hi i) n
  let α (i : I) := (Sheaf.H.map (bi i) n).comp (eHE i).hom.hom
  let α₀ := (Sheaf.H.map b n).comp eBE.hom.hom
  let β : Sheaf.H K.pt n →+ Sheaf.H L.pt (n + 1) := Sheaf.H.δSucc hS n
  refine continuation E ψ hidE hcompE GE eGE hGE LE hLE HE eHE hHE BE eBE hBE
    R ρ hidentityR hcompositionR T eT hT K hK δ α α₀ β ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hlegs⟩
  · intro i
    have : Injective (E i) := hinj i
    exact Sheaf.H.δSucc_surjective (hi i) n
  · intro i v
    exact (Sheaf.H.exact_map_δSucc (hi i) n _).2 ⟨(eHE i).hom.hom v, rfl⟩
  · intro j k g z
    have h := cohomology_boundary_naturality (D.map g.op)
      (ShortComplex.mk (ai j) (bi j) (wi j)) (hi j)
      (ShortComplex.mk (ai k) (bi k) (wi k)) (hi k) (r j k g) n z
    rw [hr₁ j k g, hr₃ j k g] at h
    exact h.symm
  · intro k z
    have h := cohomology_boundary_naturality (c.π.app (op k))
      (ShortComplex.mk (ai k) (bi k) (wi k)) (hi k)
      (ShortComplex.mk a b w) hS (t k) n z
    rw [ht₁ k, ht₃ k] at h
    exact h.symm
  · intro k v
    change Sheaf.H.map ((eT k).inv ≫ K.ι.app k) n
        (cohomologyMap (c.π.app (op k)) (R k) n
          (Sheaf.H.map (bi k) n ((eHE k).hom.hom v))) =
      Sheaf.H.map b n (eBE.hom.hom ((BE.ι.app k).hom v))
    have hm := cohomology_middle_naturality (c.π.app (op k))
      (ShortComplex.mk (ai k) (bi k) (wi k)) (ShortComplex.mk a b w)
      (t k) n ((eHE k).hom.hom v)
    rw [ht₃ k, ht₂ k] at hm
    have hb := congrArg (fun f ↦ f.hom v) (hBE k)
    exact hm.trans (congrArg (Sheaf.H.map b n) hb.symm)
  · intro y hy
    obtain ⟨v, hv⟩ := (Sheaf.H.exact_map_δSucc hS n y).1 hy
    refine ⟨eBE.inv.hom v, ?_⟩
    change Sheaf.H.map b n (eBE.hom.hom (eBE.inv.hom v)) = y
    simpa using hv


end AlgebraicGeometry.Etale
