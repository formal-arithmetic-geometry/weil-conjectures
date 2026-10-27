/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Sheaf.Paper.PointEquivariantDiagramData
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

/-- Lift the diagram at its original finite coefficient field, before coefficient extension.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, paragraph 7,
and steps 1--6 of lem-zl-point-equivariant-diagram-lift
(blueprint: lem-zl-point-equivariant-original-diagram).

Proof: Use essential surjectivity of the exact point-heart fibre equivalence to choose
objects with the given fibres, taking the prescribed object and its fibre isomorphism
literally at iStar. Lift all conjugated diagram arrows by fullness. Faithfulness proves
identity, composition and every parallel-arrow relation. Frobenius pullback preserves
the heart by constructible truncation compatibility. Its point transport is invertible.
Lift the fibre isomorphism t inverse followed by eta, A and eta inverse through the
fully faithful heart fibre functor. Lifting its inverse gives an actual Weil isomorphism.
Naturality of transport and A-equivariance make these isomorphisms natural in the
index. The prescribed compatibility and faithfulness identify its iStar component
with thetaStar. The exact fibre equivalence reflects monomorphisms, short exactness
and the universal property of cokernels. The preimage isomorphism realizes the
forward fibre formula; its inverse and Frobenius identity are computed by the caller. For the Shrink
coefficient model, transport the
exact point-heart equivalence along the canonical Shrink algebra equivalence using
the specified scalar/fibre comparison; its unit and inverse comparisons identify
this with the recorded H^0 fibre functor. -/
theorem zl_point_equivariant_original_diagram
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
      ZlDiagramExactRealization (zlDiagramHeart D l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) G hG) V ∧
      (∀ i,
        (t i).hom = zlDiagramTransport D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) (G.obj i) ∧
        (zlDiagramFiber D l hl
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)).map (theta.app i).hom =
          (t i).inv ≫ (eta.app i).hom ≫ (A i).hom ≫ (eta.app i).inv) ∧
      G.obj iStar = MStar.obj ∧ HEq (theta.app iStar) thetaStar ∧
      HEq (eta.app iStar) etaStar := by
  sorry

end WeilConjectures
