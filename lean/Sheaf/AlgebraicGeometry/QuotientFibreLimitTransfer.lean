/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Limits

/-! # Quotient closed fibres of directed limits

Source: Stacks Project, Tags 0GS2 and 0A0P.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Taking quotients by inverse-image ideals commutes with a directed scheme limit.

Source: Stacks Project, Tag 0GS2, General case, the quotient-ring and closed-fibre
limit paragraphs; Tags 01YW and 01YX for affine inverse limits.
(blueprint: lem-weil-pbc-quotient-fibre-limit-transfer).

Proof: For each index set K_i to the inverse image of I under alpha_i. Naturality
of alpha ensures that every ring transition sends K_i into K_j. Define the quotient
ring diagram using Ideal.quotientMap. Its cocone to A/I is colimiting: represent
elements of A by stage elements, and observe that an element mapping into I already
lies in K_i. Equivalently a compatible family of maps from the quotient stages
induces a unique map from A killing I and hence a unique map from A/I. Apply Spec
and its preservation of these limits. Form D stagewise by pullback of g_i along
Spec(B_i/K_i) to Spec B_i. The naturality squares induce the transition maps and
the cone from the closed fibre of Y. Pullback universality gives the two projection
equations. Limits commute with pullbacks: compatible maps to all D_i are precisely
compatible maps to all X_i and Spec(B_i/K_i) agreeing in Spec B_i. The supplied
limit and colimit identify these with maps to Y and Spec(A/I) agreeing in Spec A,
which proves the limiting property. Each transition factors through the pullback
of X_j to X_i as a closed immersion, followed by a base change of the given affine
transition of Xs, so it is affine. Choose D_i to be the indicated pullback, so the
stage isomorphisms can be identities. This holds for I = top (empty fibres), I = 0,
noninjective alpha_i, and the zero ring; no properness is required. -/
theorem quotient_fibre_limit_transfer
    {A : Type u} [CommRing A] (I : Ideal A)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (B : Λ ⥤ CommRingCat.{u}) (Xs : Λᵒᵖ ⥤ Scheme.{u})
    (g : Xs ⟶ B.op ⋙ Scheme.Spec)
    (α : B ⟶ (Functor.const Λ).obj (.of A))
    (p : (Functor.const Λᵒᵖ).obj Y ⟶ Xs)
    (hc : Nonempty (IsColimit (Cocone.mk _ α)))
    (hl : Nonempty (IsLimit (Cone.mk _ p)))
    (ha : ∀ {i j : Λᵒᵖ} (a : i ⟶ j), IsAffineHom (Xs.map a))
    (hw : ∀ i, p.app i ≫ g.app i = f ≫ Spec.map (α.app i.unop)) :
    ∃ (D : Λᵒᵖ ⥤ Scheme.{u})
      (π : (Functor.const Λᵒᵖ).obj
        (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ⟶ D),
      Nonempty (IsLimit (Cone.mk _ π)) ∧
      (∀ {i j : Λᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)) ∧
      ∀ i : Λᵒᵖ,
        ∃ e : D.obj i ≅ pullback (g.app i) (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I.comap (α.app i.unop).hom)))),
          pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ p.app i =
            (π.app i ≫ e.hom) ≫ pullback.fst (g.app i) (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I.comap (α.app i.unop).hom)))) ∧
          (π.app i ≫ e.hom) ≫ pullback.snd (g.app i) (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I.comap (α.app i.unop).hom)))) =
            pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫
              Spec.map (CommRingCat.ofHom (Ideal.quotientMap I (α.app i.unop).hom
                le_rfl)) := by sorry

end AlgebraicGeometry.Scheme
