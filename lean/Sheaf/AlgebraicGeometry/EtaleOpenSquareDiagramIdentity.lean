/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone

/-! # Identity law for coefficient restriction between two diagrams

Source: Stacks Project, Tags 09YQ and 03CB.
(blueprint: lem-weil-pbc-open-square-diagram-identity).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Restricting an identity coefficient across the identity square gives the canonical unit.
Source: Stacks Project, Tag 09YQ (coherent coefficient systems), and sites.tex,
Tag 03CB (composition of inverse images), with the unit coherence of the chosen adjoints.
(blueprint: lem-weil-pbc-open-square-diagram-identity).

Proof: Fix j. Use hF' to identify the given restricted sheaf with a_j^*F_sigma(j)
and hψ to identify its coefficient map with the explicit square coefficient.
Substitute the original identity equation for the coefficient map.
The equality D.map_id identifies the underlying transition with the scheme identity;
E.map_id similarly identifies the restricted transition with its scheme identity.
Transport along these two equalities, retaining the eqToIso factors in the statement.
The square coefficient is now the inverse of the composition isomorphism for the
identity on E_j and a_j, followed by the composition isomorphism for a_j and the
identity on D_sigma(j), followed by a_j^* of the original unit. Apply the left unit
law upperStarComp_id_left and the right unit law upperStarComp_id_right. Their
components express the first factor as the restricted unit and the second as the
inverse of a_j^* of the original unit. Functoriality cancels the latter with the
last factor. The remaining map is the restricted unit, with the E.map_id transport
restored. No injectivity, directedness, scheme limit, or nonempty open is used;
the argument also covers zero coefficients and empty schemes. -/
theorem openSquareCoefficient_diagram_identity
    {I J : Type u} [Preorder I] [Preorder J]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (E : Jᵒᵖ ⥤ Scheme.{u}) (σ : J → I)
    (a : ∀ j, E.obj (op j) ⟶ D.obj (op (σ j)))
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (h : ∀ j, a j ≫ D.map (homOfLE (le_refl (σ j))).op =
      E.map (homOfLE (le_refl j)).op ≫ a j)
    (F' : ∀ j, Sheaf (E.obj (op j)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF' : ∀ j, F' j = (upperStar AddCommGrpCat.{u + 1} (a j)).obj (F (σ j)))
    (ψ : ∀ j, (upperStar AddCommGrpCat.{u + 1}
      (E.map (homOfLE (le_refl j)).op)).obj (F' j) ⟶ F' j)
    (hψ : ∀ j, HEq (ψ j)
      (openSquareCoefficient (D.map (homOfLE (le_refl (σ j))).op) (a j) (a j)
        (E.map (homOfLE (le_refl j)).op) (h j) (F (σ j)) (F (σ j))
        (φ (homOfLE (le_refl (σ j))))))
    (j : J) :
    ψ j =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (E.map_id (op j)))).hom.app
        (F' j) ≫ (upperStarId AddCommGrpCat.{u + 1} (E.obj (op j))).hom.app (F' j) := by
  sorry

end AlgebraicGeometry.Etale
