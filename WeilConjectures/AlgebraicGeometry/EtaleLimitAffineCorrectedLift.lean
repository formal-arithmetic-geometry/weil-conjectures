/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleLimitAffineExactLadder
import WeilConjectures.AlgebraicGeometry.EtaleLimitCohomologyClassDescent
import Mathlib.CategoryTheory.Filtered.Final

/-! # Corrected lifts for the affine continuity kernel

Source: Stacks Project, Tags 09YQ, 09YP, 09YN and 0739.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- A successor-degree zero-image class has a corrected preceding-degree lift
(Stacks, Tags 09YP, 0EXZ, 0739, 0EYL and 04HR). -/
theorem etale_limit_affine_corrected_lift
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
    (n : ℕ) :
    ∃ (R : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (ρ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (R i) ⟶ R j)
    (_hidentityR : ∀ i : I, ρ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (R i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (R i))
    (_hcompositionR : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      ρ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (R i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (ρ f) ≫ ρ g)
    (T : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eT : ∀ i : I, T.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (R i))
    (_hT : ∀ (i j : I) (f : i ⟶ j), T.map f =
      (eT i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (R i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (ρ f) ≫ (eT j).inv)
    (K : Cocone T) (_hK : IsColimit K)
    (δ : ∀ k : I, Sheaf.H (R k) n →+ Sheaf.H (F k) (n + 1)),
      (∀ (j k : I) (g : j ⟶ k) (z : Sheaf.H (R j) n),
        δ k (Sheaf.H.map (ρ g) n (cohomologyMap (D.map g.op) (R j) n z)) =
          Sheaf.H.map (φ g) (n + 1)
            (cohomologyMap (D.map g.op) (F j) (n + 1) (δ j z))) ∧
      (∀ (i : I) (x : Sheaf.H (F i) (n + 1)),
        Sheaf.H.map ((eG i).inv ≫ L.ι.app i) (n + 1)
          (cohomologyMap (c.π.app (op i)) (F i) (n + 1) x) = 0 →
        ∃ (j : I) (f : i ⟶ j) (z : Sheaf.H (R j) n),
          Sheaf.H.map ((eT j).inv ≫ K.ι.app j) n
            (cohomologyMap (c.π.app (op j)) (R j) n z) = 0 ∧
          δ j z = Sheaf.H.map (φ f) (n + 1)
            (cohomologyMap (D.map f.op) (F i) (n + 1) x)) := by
  classical
  apply etale_limit_affine_exact_ladder
    D c hc F φ hidentity hcomposition G eG hG L hL n
  intro E ψ hidE hcompE GE eGE hGE LE hLE HE eHE hHE BE eBE hBE
    R ρ hidR hcompR T eT hT K hK δ α α₀ β hrows
  rcases hrows with ⟨hsurj, hzero, hδ, hδsquare, hαsquare, hexact, htrans⟩
  refine ⟨R, ρ, hidR, hcompR, T, eT, hT, K, hK, δ, hδ, ?_⟩
  intro i x hx
  obtain ⟨z₀, hz₀⟩ := hsurj i x
  have hβz : β (Sheaf.H.map ((eT i).inv ≫ K.ι.app i) n
      (cohomologyMap (c.π.app (op i)) (R i) n z₀)) = 0 := by
    rw [hδsquare, hz₀, hx]
  obtain ⟨w, hw⟩ := hexact _ hβz
  obtain ⟨k, v, hv⟩ := etale_limit_cohomology_class_descent
    D c hc E ψ hidE hcompE GE eGE hGE LE hLE n HE eHE hHE BE eBE hBE w
  let j := IsFiltered.max i k
  let f : i ⟶ j := IsFiltered.leftToMax i k
  let g : k ⟶ j := IsFiltered.rightToMax i k
  let v' := (HE.map g).hom v
  let z := Sheaf.H.map (ρ f) n (cohomologyMap (D.map f.op) (R i) n z₀) - α j v'
  refine ⟨j, f, z, ?_, ?_⟩
  · dsimp only [z]
    rw [map_sub, map_sub, htrans, hαsquare]
    have hv' : (BE.ι.app j).hom v' = w := by
      calc
        (BE.ι.app j).hom v' = (BE.ι.app k).hom v :=
          ConcreteCategory.congr_hom (BE.w g) v
        _ = w := hv
    rw [hv', hw, sub_self]
  · dsimp only [z]
    rw [map_sub, hδ, hzero, sub_zero, hz₀]


end AlgebraicGeometry.Etale
