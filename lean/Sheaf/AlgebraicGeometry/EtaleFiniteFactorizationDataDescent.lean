/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.FullAffineEtaleSite
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Descent of finite affine étale factorization data

Source: Stacks Project, Étale Cohomology Tag 0EYL (lemma-colimit-affine-sites), and
Limits Tags 01ZM and 01ZC, finite-presentation descent of objects and morphisms.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Descend finitely many affine étale sources and their two families of arrows.
No covering assumption or conclusion is involved.

Source: Stacks, Étale Cohomology 0EYL, qcqs proof; Limits 01ZM and 01ZC.
(blueprint: lem-weil-pbc-etale-finite-factorization-data-descent).

Proof: Restrict to the cofinal tail above i₀. By affine étale object and arrow
 descent, descend each affine V_q and its map to W. Choose a common stage for
 these finitely many models. For each model, its base-change diagram on the tail
 has affine transitions and affine terms, and limit V_q. Compose b_q with the
 projection to U_q. Since U_q is étale over D(i₀), its structure map is locally
 finitely presented. Limits 01ZC(3) descends this morphism from the qcqs source
 diagram without imposing quasi-compactness on U_q. Its structure equation and
 the pullback universal property give the required stage arrow into the pullback
 of U_q. Choose a common stage for the finitely many arrows and equations.
 Pullback pasting identifies the same source model with V_q for both arrows,
 giving both displayed equations. Affineness survives further base change.
 When n=0 take the identity stage and the empty families. -/
theorem etale_finiteFactorizationDataDescent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (W : (D.obj (op i₀)).FullAffineEtale)
    (n : ℕ) (V : Fin n → c.pt.Etale)
    (a : ∀ q, V q ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W.obj)
    (U : Fin n → (D.obj (op i₀)).Etale)
    (b : ∀ q, V q ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (U q))
    (hV : ∀ q, IsAffine (V q).left) :
    let B := fun j : Over (op i₀) ↦ MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)
    let F := fun j : Over (op i₀) ↦ MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)
    let e := fun (j : Over (op i₀)) (Z : (D.obj (op i₀)).Etale) ↦
      (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
        (c.π.app j.left) (D.map j.hom) (c.π.app (op i₀)) (c.w j.hom).symm).app Z
    ∃ (j : Over (op i₀)) (Vj : Fin n → (D.obj j.left).Etale)
      (aj : ∀ q, Vj q ⟶ (F j).obj W.obj)
      (bj : ∀ q, Vj q ⟶ (F j).obj (U q))
      (d : ∀ q, (B j).obj (Vj q) ≅ V q),
      (∀ q, IsAffine (Vj q).left) ∧
      (∀ q, (B j).map (aj q) ≫ (e j W.obj).inv = (d q).hom ≫ a q) ∧
      (∀ q, (B j).map (bj q) ≫ (e j (U q)).inv = (d q).hom ≫ b q) := by sorry

end AlgebraicGeometry
