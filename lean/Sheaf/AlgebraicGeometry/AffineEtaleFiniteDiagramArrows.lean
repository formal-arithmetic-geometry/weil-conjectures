/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.FullAffineEtaleSite
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Eventual lifting of arrows between affine étale models

Source: Stacks Project, Étale Cohomology 0EYL and Limits 01ZM.
(blueprint: lem-pbc-affine-etale-model-arrows).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Limits 01ZM(2), and Étale Cohomology 0EYL.

Proof: Use the q-pullback squares to identify the v-images with canonical pullbacks.
For each arrow apply 01ZM(2) to the two fixed affine étale models, which are finitely
presented over the stage. It gives a later stage and an arrow between their base
changes. Take an upper bound for these finitely many stages and the original
stage, then pull back the arrows to that bound. Affine transition maps ensure that
the base-changed models are still affine, and étaleness is preserved by base change.
Transitivity and uniqueness of pullbacks give comparison isomorphisms from their
v-images to the original v-images. Naturality of q and pullback uniqueness identify
the lifted arrows with the given arrows under those isomorphisms. For no arrows,
take the original stage and the identity base-change comparisons.
(blueprint: lem-pbc-affine-etale-model-arrows). -/
theorem affineEtale_model_arrows
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ (i : Iᵒᵖ), CompactSpace (D.obj i)]
    [∀ (i : Iᵒᵖ), QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c)
      (v : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ c.pt.FullAffineEtale)
      (q : ∀ i : I,
        v i ⋙ fullAffineEtaleInclusion c.pt ⋙ Etale.forget c.pt ⋙ Over.forget c.pt ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
    (h2 : (∀ (i : I) (A : (D.obj (op i)).FullAffineEtale),
        IsPullback ((q i).app A) ((v i).obj A).obj.hom A.obj.hom (c.π.app (op i))))
    (i : I) (n : ℕ) (Ai : (D.obj (op i)).FullAffineEtale)
    (Bi : Fin n → (D.obj (op i)).FullAffineEtale)
    (g : ∀ a : Fin n, (v i).obj (Bi a) ⟶ (v i).obj Ai) :
    ∃ (j : I) (h : i ≤ j) (Aj : (D.obj (op j)).FullAffineEtale)
      (Bj : Fin n → (D.obj (op j)).FullAffineEtale)
      (fi : ∀ a : Fin n, Bj a ⟶ Aj)
      (rA : Aj.obj.left ⟶ Ai.obj.left)
      (rB : ∀ a : Fin n, (Bj a).obj.left ⟶ (Bi a).obj.left),
      IsPullback rA Aj.obj.hom Ai.obj.hom (D.map (homOfLE h).op) ∧
      (∀ a : Fin n,
        IsPullback (rB a) (Bj a).obj.hom (Bi a).obj.hom (D.map (homOfLE h).op)) ∧
      ∃ (t : (v j).obj Aj ≅ (v i).obj Ai)
        (s : ∀ a : Fin n, (v j).obj (Bj a) ≅ (v i).obj (Bi a)),
        ∀ a : Fin n, (v j).map (fi a) ≫ t.hom = (s a).hom ≫ g a  := by sorry

end AlgebraicGeometry.Scheme
