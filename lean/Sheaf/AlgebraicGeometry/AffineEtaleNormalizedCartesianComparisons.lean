/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.AlgebraicGeometry.FullAffineEtaleSite

/-!
# Normalized comparison isomorphisms of cartesian affine étale functors

Source: Stacks Project, Étale Cohomology 0EYL, including its coherence discussion.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Étale Cohomology 0EYL, its base-change construction and
coherence discussion following the proof.

Proof: The supplied cartesian squares determine the objects of U and v up to the
unique isomorphism respecting their first and structure projections. For i ≤ j ≤ k,
paste the two U object squares. Functoriality of D identifies the composite base arrow
with D.map (homOfLE (h.trans h')).op. Compare this pullback with the supplied single
U_ik pullback using its universal property. The resulting component isomorphisms form
gamma: after composing with the first projection, naturality is exactly naturality of
p; after composing with the structure projection it follows because the arrows are
morphisms over D_k. Pullback uniqueness therefore proves naturality. The first-projection
equation is the defining equation of this comparison. For delta use the identical
construction, pasting the U square with the v square; cone naturality identifies the
composite base arrow with c.π.app (op i).

When i = j or j = k, rewrite U_ii by hid. The supplied hpd makes its first projection
identity. The corresponding functor unitor has identity components and satisfies the
same first- and structure-projection equations as the constructed comparison. Pullback
uniqueness makes the comparisons equal to these unitors. The unitors are heterogeneously
equal to Iso.refl after the identity-composition equalities, giving all three HEq clauses.
No cocycle or site property is asserted.
(blueprint: lem-weil-pbc-affine-etale-normalized-cartesian-comparisons). -/
theorem exists_affineEtale_normalized_cartesian_comparisons
    {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (U : ∀ (i j : I), i ≤ j → (D.obj (op i)).FullAffineEtale ⥤
          (D.obj (op j)).FullAffineEtale)
      (v : ∀ i : I, (D.obj (op i)).FullAffineEtale ⥤ c.pt.FullAffineEtale)
      (p : ∀ (i j : I) (h : i ≤ j),
        U i j h ⋙ fullAffineEtaleInclusion (D.obj (op j)) ⋙
          Etale.forget (D.obj (op j)) ⋙ Over.forget (D.obj (op j)) ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
      (q : ∀ i : I,
        v i ⋙ fullAffineEtaleInclusion c.pt ⋙ Etale.forget c.pt ⋙ Over.forget c.pt ⟶
        fullAffineEtaleInclusion (D.obj (op i)) ⋙
          Etale.forget (D.obj (op i)) ⋙ Over.forget (D.obj (op i)))
    (hid : ∀ i : I, U i i le_rfl = 𝟭 _)
    (hpd : ∀ (i : I) (A : (D.obj (op i)).FullAffineEtale),
      HEq ((p i i le_rfl).app A) (𝟙 A.obj.left))
    (hp : ∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
      IsPullback ((p i j h).app A) ((U i j h).obj A).obj.hom
        A.obj.hom (D.map (homOfLE h).op))
    (hq : ∀ (i : I) (A : (D.obj (op i)).FullAffineEtale),
      IsPullback ((q i).app A) ((v i).obj A).obj.hom A.obj.hom (c.π.app (op i))) :
    ∃ (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
        U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
      (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i),
      (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
      ∧ (∀ (i k : I) (h : i ≤ k),
        HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
      ∧ (∀ i : I, HEq (delta i i le_rfl) (Iso.refl (v i)))
      ∧ (∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k)
        (A : (D.obj (op i)).FullAffineEtale),
        ((gamma i j k h h').hom.app A).hom.left ≫ (p i k (h.trans h')).app A =
          (p j k h').app ((U i j h).obj A) ≫ (p i j h).app A)
      ∧ (∀ (i j : I) (h : i ≤ j) (A : (D.obj (op i)).FullAffineEtale),
        ((delta i j h).hom.app A).hom.left ≫ (q i).app A =
          (q j).app ((U i j h).obj A) ≫ (p i j h).app A) := by sorry

end AlgebraicGeometry.Scheme
