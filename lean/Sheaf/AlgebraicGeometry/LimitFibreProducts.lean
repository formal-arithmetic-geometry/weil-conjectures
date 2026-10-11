/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.LimitResidueField
import Sheaf.AlgebraicGeometry.FibreProductLimit

/-!
# Fibre products commute with limits along affine transition morphisms

Source: Stacks Project, Derived Categories, proof of Lemma 0G7X (line 8166),
with Categories Lemma 002M and Morphisms Lemmas 01SD, 01SC, 01SG
(blueprint: lem-weil-pbc-limit-fibre-products).
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Fibre products and scheme-theoretic fibres commute with the given affine-transition
limits, including their canonical projections. Equalities of objects and `HEq` of maps
identify the chosen representatives without introducing extra isomorphism choices.

Source: Stacks Project, proof of Lemma 0G7X, the limit argument, and Tags 002M,
01SD, 01SC, 01SG (blueprint: lem-weil-pbc-limit-fibre-products).

Proof:
1. The limits of X, S and T exist by `exists_limit_affine_transition`
   (lem-weil-pbc-limit-affine-transition). For the chosen limit cones, their universal
   properties define F and G uniquely by hF and hG. Apply the categorical comparison
   `Scheme.isIso_limit_pullback_comparison` (lem-kun-fibre-product-limits): compatible
   maps to the stage pullbacks are precisely compatible pairs of maps to X and T
   with equal composites to S. Thus the indicated pullback cone is limiting.
2. Each transition between stage pullbacks is affine by
   lem-weil-pbc-fibre-product-affine-transition: factor via the affine diagonal of
   the base transition and the base changes of the affine transitions on X and T.
   Use stability under base change and composition (01SD, 01SC, 01SG).
3. `exists_isColimit_residueField_of_isLimit` (lem-weil-pbc-limit-residue-field)
   identifies the residue-field point of s with the limit of its stage points.
   Apply steps 1 and 2 to X, S and these residue-field spectra. This gives the
   limiting fibre cone with affine transitions and the stated projections to X.
   The fibre embeddings are monomorphisms, so these projection identities uniquely
   determine both the canonical transition maps and the cone maps. -/
theorem limit_fibre_products_of_affine_transition
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (X S T : Iᵒᵖ ⥤ Scheme.{u})
    (f : X ⟶ S) (g : T ⟶ S)
    [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (X.map h)]
    [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (S.map h)]
    [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (T.map h)]
    (cX : Cone X) (hcX : IsLimit cX)
    (cS : Cone S) (hcS : IsLimit cS)
    (cT : Cone T) (hcT : IsLimit cT)
    (F : cX.pt ⟶ cS.pt) (G : cT.pt ⟶ cS.pt)
    (hF : ∀ i : Iᵒᵖ, F ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    (hG : ∀ i : Iᵒᵖ, G ≫ cS.π.app i = cT.π.app i ≫ g.app i) :
    (∃ (P : Iᵒᵖ ⥤ Scheme.{u}) (a : P ⟶ X) (b : P ⟶ T) (cP : Cone P),
      (∀ i : Iᵒᵖ, P.obj i = pullback (f.app i) (g.app i)) ∧
      (∀ i : Iᵒᵖ, HEq (a.app i) (pullback.fst (f.app i) (g.app i))) ∧
      (∀ i : Iᵒᵖ, HEq (b.app i) (pullback.snd (f.app i) (g.app i))) ∧
      (∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (P.map h)) ∧
      cP.pt = pullback F G ∧
      (∀ i : Iᵒᵖ, HEq (cP.π.app i ≫ a.app i)
        (pullback.fst F G ≫ cX.π.app i)) ∧
      (∀ i : Iᵒᵖ, HEq (cP.π.app i ≫ b.app i)
        (pullback.snd F G ≫ cT.π.app i)) ∧
      Nonempty (IsLimit cP)) ∧
    (∀ s : cS.pt, ∃ (Q : Iᵒᵖ ⥤ Scheme.{u}) (a : Q ⟶ X) (cQ : Cone Q),
      (∀ i : Iᵒᵖ, Q.obj i = (f.app i).fiber (cS.π.app i s)) ∧
      (∀ i : Iᵒᵖ, HEq (a.app i) ((f.app i).fiberι (cS.π.app i s))) ∧
      (∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (Q.map h)) ∧
      cQ.pt = F.fiber s ∧
      (∀ i : Iᵒᵖ, HEq (cQ.π.app i ≫ a.app i) (F.fiberι s ≫ cX.π.app i)) ∧
      Nonempty (IsLimit cQ)) := by
  sorry

end AlgebraicGeometry
