/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.EtaleLimitReplacementExactSystems
import WeilConjectures.AlgebraicGeometry.EtaleLimitInjectiveColimitAcyclic
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder

/-! # Acyclic replacement of an inverse system of etale sheaves

Source: Stacks Project, Tags 09YP, 0EXZ, 0739, 09YN and 09YQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option linter.unusedVariables false in
/-- Compatible injective embeddings give a short exact limit sequence with acyclic middle term
(Stacks, Tags 09YP, 0EXZ, 0739, 09YQ, 09YN, 0EYL and 04HR). -/
theorem etale_limit_acyclic_replacement
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
    (L : Cocone G) (hL : IsColimit L) (n : ℕ) :
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
    (E : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : L.pt ⟶ E) (b : E ⟶ LR.pt) (w : a ≫ b = 0)
    (hE : (ShortComplex.mk a b w).ShortExact)
    (d : AddCommGrpCat.of (Sheaf.H LR.pt n) ⟶
      AddCommGrpCat.of (Sheaf.H L.pt (n + 1))),
      (∀ x, d.hom x = Abelian.Ext.comp x hE.extClass rfl) ∧
      Subsingleton (Sheaf.H E (n + 1)) ∧
      ∃ beta : ∀ i : I, AddCommGrpCat.of (Sheaf.H (FR i) n) ⟶
        AddCommGrpCat.of (Sheaf.H (F i) (n + 1)),
        ∀ i : I,
          beta i ≫ AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (F i) (n + 1)) ≫
            AddCommGrpCat.ofHom (Sheaf.H.map ((eG i).inv ≫ L.ι.app i) (n + 1)) =
          AddCommGrpCat.ofHom (cohomologyMap (c.π.app (op i)) (FR i) n) ≫
            AddCommGrpCat.ofHom (Sheaf.H.map ((eGR i).inv ≫ LR.ι.app i) n) ≫ d
    := by
  classical
  obtain ⟨FR, φR, hidentityR, hcompositionR, GR, eGR, hGR, LR, hLR,
      FI, ψ, hidentityI, hcompositionI, GI, eGI, hGI, LI, hLI, a, b, w, hE,
      ai, bi, wi, hi, t, hinj, ht1, ht3⟩ :=
    etale_limit_replacement_exact_systems
      D c hc F φ hidentity hcomposition G eG hG L hL
  have hacyclic := etale_limit_injective_colimit_acyclic
    D c hc FI ψ hidentityI hcompositionI GI eGI hGI LI hLI hinj n
  let d := AddCommGrpCat.ofHom (Sheaf.H.δSucc hE n)
  let beta (i : I) := AddCommGrpCat.ofHom (Sheaf.H.δSucc (hi i) n)
  refine ⟨FR, φR, hidentityR, hcompositionR, GR, eGR, hGR, LR, hLR,
    LI.pt, a, b, w, hE, d, ?_, hacyclic, beta, ?_⟩
  · intro x
    rfl
  · intro i
    obtain ⟨hY, δX, δY, hδX, hδY, _, _, _, _, _, _, hδ⟩ :=
      pullbackCohomology_longExact_ladder (c.π.app (op i))
        (ShortComplex.mk (ai i) (bi i) (wi i)) (hi i)
    ext x
    change Sheaf.H.map ((eG i).inv ≫ L.ι.app i) (n + 1)
        (cohomologyMap (c.π.app (op i)) (F i) (n + 1)
          (Sheaf.H.δSucc (hi i) n x)) =
      Sheaf.H.δSucc hE n (Sheaf.H.map ((eGR i).inv ≫ LR.ι.app i) n
        (cohomologyMap (c.π.app (op i)) (FR i) n x))
    have hp : cohomologyMap (c.π.app (op i)) (F i) (n + 1)
        (Sheaf.H.δSucc (hi i) n x) =
      Sheaf.H.δSucc hY n (cohomologyMap (c.π.app (op i)) (FR i) n x) := by
      rw [Sheaf.H.δSucc_apply, Sheaf.H.δSucc_apply]
      simpa only [hδX n x, hδY] using hδ n x
    rw [hp, ← ht1 i, ← ht3 i]
    exact Sheaf.H.map_δSucc hY hE (t i) n _


end AlgebraicGeometry.Etale
