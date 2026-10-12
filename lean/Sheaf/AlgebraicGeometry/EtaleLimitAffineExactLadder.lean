/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Exact connecting ladders for affine-stage cohomology

Source: Stacks Project, Tags 09YQ, 09YP, 09YN and 0739.
(blueprint: lem-weil-pbc-etale-limit-affine-exact-ladder).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Exact connecting rows and their comparison squares for an affine-stage system.

Source: Stacks Project, Tag 09YP, using 0EXZ and the right-exact rows of 0739;
scheme-to-affine-site comparison in 0EYL and 04HR.
(blueprint: lem-weil-pbc-etale-limit-affine-exact-ladder).

Proof: Embed the system F in the injective system E of 0EXZ. At i, form the
product of the direct images of injective embeddings of F_k over all i → k.
Adjunction transposes the coefficient transitions followed by these embeddings.
The identity component makes F_i → E_i monic. Direct images preserve injectives
because their left adjoints are exact, and products of injectives are injective.
Their canonical transitions satisfy the two inverse-image coherence laws.
Take cokernels R_i; exact inverse image and cancellation of the cokernel epis
supply ρ, its identity and composition equations. Pull E and R to the limit,
with the composition comparisons, obtaining GE and T. Take their colimits LE
and K. Exact filtered colimits of abelian sheaves give 0 → L → LE → K → 0.

Form HE from degree-n cohomology of E_i, with transition ψ after pullback, and
BE with vertex H^n(LE) and the displayed legs. Pullback functoriality and the
coefficient cocycle prove the diagram and cocone laws. The identity isos give
eHE and eBE. The degree-n map E_i → R_i induces α_i after eHE. The stage
connecting map is δ_i, and the corresponding limit maps are α₀ and β.
Stage injectivity makes δ_i surjective since H^(n+1)(E_i)=0. Exactness of the
stage sequence gives δ_i α_i=0. Naturality of the long exact sequence under
exact inverse image gives δ-transition compatibility. Naturality for the
limit coprojections gives the β-δ and α₀-α squares. Exactness of the limit
sequence at H^n(K) gives ker β = im α₀, without needing any acyclicity of LE.
The R comparison legs commute with transitions by pullback composition,
coefficient naturality, the cocycle for T, and the cocone law for K. All
comparisons are unit compatible under affine restriction and strictification:
the right adjoints evaluate on the same cartesian base changes, so uniqueness
of their left adjoints gives the comparisons and their coherence.

No cohomological continuity in any degree is claimed by this ladder. In
particular class descent and eventual detection of zero are separate steps.
For n=0 exactness is at H⁰(K); for an empty scheme all groups are zero.
-/
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
          (cohomologyMap (c.π.app (op j)) (R j) n z)) → result) : result := by sorry

end AlgebraicGeometry.Etale
