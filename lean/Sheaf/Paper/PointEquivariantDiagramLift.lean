/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.Paper.PointEquivariantDiagramData
import Sheaf.Paper.PointEquivariantOriginalDiagram
import Sheaf.Paper.PointEquivariantFiniteScalar
import Sheaf.Paper.PointEquivariantCommonStage

/-! # Lifting a point diagram and its coefficient extensions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Lift an entire finite equivariant vector-space diagram to the raw constructible
Weil heart, keeping the prescribed object and its fibre identification literally.
All inverse maps and exact diagrams are over the original finite coefficient field;
finite extensions and the closure use the specified scalar and transport comparisons.
No continuity, finite-order condition or semisimplicity is assumed on the automorphisms.

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph 7
(blueprint: lem-zl-point-equivariant-diagram-lift).

Proof: (1) Use the exact point-heart equivalence of lem-zl-point-heart-finite-stage
for objects away from iStar, taking MStar and etaStar literally at iStar.
(2) Truncation compatibility puts T(M) in the heart. Invertibility of point transport
(lem-weil-frobenius-cohomology-transport-iso) gives t. Fullness lifts
eta A eta inverse after t inverse, and its inverse; faithfulness proves both inverse
identities and identifies the prescribed thetaStar.
(3) Lift each arrow by fullness. Cancelling intermediate eta components proves
identities, compositions and every path relation by faithfulness.
(4) Naturality of point transport (lem-weil-frobenius-point-transport-natural)
and the given A-equivariance prove the Weil commuting square by faithfulness.
(5) The exact point-heart equivalence reflects short exact sequences, monos and
cokernels, including their universal properties.
(6) The local Frobenius is H^0(iota) followed by H^0(theta), so conjugation by eta
cancels t and t inverse and yields A. The same computation covers zero spaces and
nonsemisimple Jordan blocks.
(7) Extend theta using the inverse normalized pullback/scalar comparison and extend
eta using the normalized point-fibre/cohomology comparison. Scalar compatibility
of point transport gives the displayed transport square, so the same fibre formulas
and exactness hold over every finite overfield.
(8) Include the entire diagram at its original common stage. All relations and inverse
identities already hold there. Constructible truncations put it in the common-stage
heart, and exact field extension followed by reflection under the point-heart
equivalence gives its exact sequences and cokernels. The normalized common-stage
transport identifies Frobenius with A tensor 1 and preserves the prescribed object. -/
theorem zl_point_equivariant_diagram_lift
    (F : Padic.FiniteCoefficientFields l Ω)
    (I : Type w) [SmallCategory I] [FinCategory I]
    (V : I ⥤ ModuleCat.{u} (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F))
    (hV : ∀ i, FiniteDimensional (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
      (V.obj i))
    (A : ∀ i, V.obj i ≅ V.obj i)
    (hA : ∀ {i j : I} (f : i ⟶ j), (A i).hom ≫ V.map f = V.map f ≫ (A j).hom)
    (iStar : I)
    (MStar : sfRationalHeart l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
      (Spec (.of D.k)))
    (thetaStar : (zlDiagramPullback D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj MStar.obj ≅ MStar.obj)
    (etaStar : (zlDiagramFiber D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj MStar.obj ≅ V.obj iStar)
    (hStar : etaStar.inv ≫ zlDiagramTransport D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) MStar.obj ≫
      (zlDiagramFiber D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).map
        thetaStar.hom ≫ etaStar.hom = (A iStar).hom) :
    ∃ (G : I ⥤ sfRationalConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) (Spec (.of D.k)))
      (hG : ∀ i, sfRationalHeartProperty l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) (Spec (.of D.k)) (G.obj i))
      (theta : G ⋙ zlDiagramPullback D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) ≅ G)
      (eta : G ⋙ zlDiagramFiber D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) ≅ V)
      (t : ∀ i, (zlDiagramFiber D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj (G.obj i) ≅
        (zlDiagramFiber D l hl (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj
          ((zlDiagramPullback D l hl
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).obj (G.obj i))),
      ZlPointDiagramRealization D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) V A G hG theta eta t ∧
      G.obj iStar = MStar.obj ∧ HEq (theta.app iStar) thetaStar ∧
      HEq (eta.app iStar) etaStar ∧
      (∀ (L' : Padic.FiniteCoefficientFields l Ω) (h : F ≤ L'),
        ZlFiniteScalarDiagram D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L')
          (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F L' h)
          V A G theta eta t) ∧
      ZlCommonStageDiagram D l hl Ω F V A G theta eta t := by
  obtain ⟨G, hG, theta, eta, t, hexact, hmaps, hobj, htheta, heta⟩ :=
    zl_point_equivariant_original_diagram D l hl Ω F I V hV A hA
      iStar MStar thetaStar etaStar hStar
  have hreal : ZlPointDiagramRealization D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) V A G hG theta eta t := by
    refine ⟨hexact, fun i ↦ ?_⟩
    obtain ⟨ht, hforward⟩ := hmaps i
    have he : (zlDiagramFiber D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).mapIso (theta.app i) =
        (t i).symm ≪≫ eta.app i ≪≫ A i ≪≫ (eta.app i).symm := Iso.ext hforward
    refine ⟨ht, hforward, ?_, ?_⟩
    · simpa only [Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv, Category.assoc] using
        congrArg Iso.inv he
    · rw [hforward]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
        Iso.inv_hom_id, Category.comp_id]
  refine ⟨G, hG, theta, eta, t, hreal, hobj, htheta, heta, ?_, ?_⟩
  · intro L' h
    exact zl_point_equivariant_finite_scalar D l hl _ _
      (AlgebraicallyClosedCoefficients.coefficientInclusion.{u} l Ω F L' h)
      V A G hG theta eta t hreal
  · exact zl_point_equivariant_common_stage D l hl Ω F V A G hG theta eta t hreal

end WeilConjectures
