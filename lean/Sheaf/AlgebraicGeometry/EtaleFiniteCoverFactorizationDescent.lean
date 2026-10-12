/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.FullAffineEtaleSite
import Sheaf.AlgebraicGeometry.AffineEtaleCoveringEventually
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Descent of a finite affine covering with finitely many factorizations

Source: Stacks Project, Étale Cohomology Tag 0EYL (lemma-colimit-affine-sites), and
Limits Tags 01ZM and 01ZC, finite-presentation descent of objects and morphisms.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A finite affine covering of a fixed base-changed object, together with one map from
 each covering object into a base-changed original étale object, descends to a common
 stage. This is a geometric assertion: it contains no sheaf or section.

Source: Stacks Project, Étale Cohomology Tag 0EYL (lemma-colimit-affine-sites), qcqs case,
and Limits Tags 01ZM and 01ZC, descent of finite-presentation objects and arrows.
(blueprint: lem-weil-pbc-etale-finite-cover-factorization-descent).

Proof: Work on the cofinal tail above i₀. Each affine étale V_q has finite presentation
 over the qcqs limit scheme. Descend its object and its arrow into the fixed affine
 W using the object and arrow clauses of the affine étale site colimit. For each
 arrow b_q into the possibly non-affine base change of U_q, consider the inverse
 system of base changes of the descended affine source on its tail. Its transition
 maps are affine, its terms are affine (hence qcqs), and its limit is V_q by base
 change of limits. Composing b_q with the projection to U_q gives a morphism over
 the original base D(i₀). The structure morphism of U_q is étale, hence locally
 of finite presentation. Apply 01ZC(3), or Mathlib's
 Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation, to descend this
 morphism over D(i₀). The pullback universal property converts it to a map
 into the stage base change of U_q. No quasi-compactness or separation assumption
 on U_q is needed. Choose a common stage for this finite collection of
 data and equations. The maps to W and U_q then base change to a_q and b_q under
 the same source isomorphism d_q; these are the displayed equations with the
 canonical pullback-composition isomorphisms. Finally the finite union of images
 of the descended arrows to W is constructible. Since it covers W at the limit,
 covering descent makes it cover at a later stage. Base change preserves the
 factorization equations and affineness. When n = 0, covering descent says that
 the fixed test object becomes empty at a later stage; no factorization data is
 required. -/
theorem etale_finiteCoverFactorizationDescent
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
    (ha : Sieve.ofArrows V a ∈ c.pt.smallEtaleTopology
      ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj W.obj))
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
      Sieve.ofArrows Vj aj ∈ (D.obj j.left).smallEtaleTopology ((F j).obj W.obj) ∧
      (∀ q, IsAffine (Vj q).left) ∧
      (∀ q, (B j).map (aj q) ≫ (e j W.obj).inv = (d q).hom ≫ a q) ∧
      (∀ q, (B j).map (bj q) ≫ (e j (U q)).inv = (d q).hom ≫ b q) := by sorry

end AlgebraicGeometry
