/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.ProfinitePointPullback
public import Sheaf.Paper.PointLanAffineEvaluation
import Sheaf.Paper.ProEtalePointComponentsMaps
import Sheaf.Paper.ProEtaleSheafificationWcontractibleSections

/-!
# The point-pullback formula on the weakly contractible affine basis

Source: Bhatt–Scholze, Lemma 4.2.13(1); Hemo–Richarz–Scholbach, Example 3.1;
RefactorInstruction, Section 4, Lemma point-eval
(blueprint: lem-weil-pbc-condensed-point-basis-evaluation).
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The commutative-ring inverse image is the geometric inverse image `π_X⁻¹ a*`,
constructed by left Kan extension and sheafification in commutative rings.
Source: RefactorInstruction, Section 4, prop:pX and Lemma point-eval
(blueprint: lem-weil-pbc-condensed-point-basis-evaluation). -/
noncomputable abbrev pointBasisRingInverseImage (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafPullback profiniteToProEt CommRingCat.{u + 1}
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ) ⋙
      Scheme.proEtaleSheafInverseImage (toSpecZ X) CommRingCat.{u + 1}

/-- The evaluation formula, simultaneously natural in the coefficient sheaf and in
morphisms of weakly contractible affine objects. Isomorphisms are taken in `C`, so
in the algebraic coefficient categories they preserve the corresponding operations.
`pointLanComponents` is the actual connected-component quotient, not a chosen space.
Source: RefactorInstruction, Section 4, Lemma point-eval
(blueprint: lem-weil-pbc-condensed-point-basis-evaluation). -/
def PointBasisEvaluationProperty (X : Scheme.{u}) (C : Type w) [Category.{v} C]
    (L : Sheaf (coherentTopology Profinite.{u}) C ⥤
      Sheaf (Scheme.ProEt.topology X) C) : Prop :=
  ∃ e : ∀ (F : Sheaf (coherentTopology Profinite.{u}) C)
      (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U),
      (L.obj F).obj.obj (op U) ≅ F.obj.obj (op (pointLanComponents X U hU wU)),
    (∀ (F G : Sheaf (coherentTopology Profinite.{u}) C) (α : F ⟶ G)
      (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U),
      (L.map α).hom.app (op U) ≫ (e G U hU wU).hom =
        (e F U hU wU).hom ≫ α.hom.app (op (pointLanComponents X U hU wU))) ∧
    (∀ (F : Sheaf (coherentTopology Profinite.{u}) C)
      (U V : X.ProEt) (hU : IsAffine U.left) (hV : IsAffine V.left)
      (wU : PointLanWeaklyContractible X U) (wV : PointLanWeaklyContractible X V)
      (a : V ⟶ U),
      (L.obj F).obj.map a.op ≫ (e F V hV wV).hom =
        (e F U hU wU).hom ≫ F.obj.map
          (ConcreteCategory.ofHom
            ⟨a.left.continuous.connectedComponentsMap,
              a.left.continuous.connectedComponentsMap_continuous⟩ :
            pointLanComponents X V hV wV ⟶ pointLanComponents X U hU wU).op)

/-- The geometric inverse image of a condensed set, abelian group, or commutative ring
on a weakly contractible affine is its value on the profinite component quotient.
The identifications are natural in both variables and preserve the algebraic operations.
The final clause records the quotient topology explicitly.

Source: Bhatt–Scholze, Lemma 4.2.13(1), inverse-image computation;
Hemo–Richarz–Scholbach, Example 3.1; RefactorInstruction, Section 4, Lemma point-eval
(blueprint: lem-weil-pbc-condensed-point-basis-evaluation).

Proof for stage 3:
1. Apply lem-weil-pbc-proetale-point-components-maps to obtain the profinite quotient
   and the natural bijection Hom_X(U,X[S]) = C(pi_0(U),S).
2. The left Kan extension is evaluation at this quotient: the identity of pi_0(U)
   gives a terminal object of the Kan indexing category. This is the computation in
   lem-weil-pbc-point-lan-affine-evaluation. Identify the relative inverse image with
   π_X⁻¹ a* using the inverse-image composition comparison of
   lem-weil-pbc-profinite-point-pullback.
3. By lem-weil-pbc-proetale-sheafification-wcontractible-sections, the sheafification
   unit on U is invertible. Compose its inverse with the Kan evaluation isomorphism.
   Naturality of the Kan comparison and the unit gives both naturality equations.
4. The same construction in abelian groups and commutative rings is an isomorphism
   in that category, so it preserves addition and multiplication when present.
   The topology of ConnectedComponents is the quotient topology by definition. -/
theorem condensed_point_basis_evaluation (X : Scheme.{u}) :
    PointBasisEvaluationProperty X (Type (u + 1))
      (profinitePointSetSchemeInverseImage X) ∧
    PointBasisEvaluationProperty X AddCommGrpCat.{u + 1} (upperStarFromPoint X) ∧
    PointBasisEvaluationProperty X CommRingCat.{u + 1} (pointBasisRingInverseImage X) ∧
    (∀ (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U),
      CompactSpace (pointLanComponents X U hU wU) ∧
      T2Space (pointLanComponents X U hU wU) ∧
      TotallyDisconnectedSpace (pointLanComponents X U hU wU) ∧
      ∀ s : Set (ConnectedComponents U.left),
        IsOpen s ↔ IsOpen (ConnectedComponents.mk ⁻¹' s)) := by
  sorry

end AlgebraicGeometry.ProEtale
