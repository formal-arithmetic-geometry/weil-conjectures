/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.DisjointCover
public import WeilConjectures.SixFunctors.Finite.Stalk

/-!
# Pointed clopen refinements for integral morphisms

Source: the conservativity argument in the proof of blueprint `sbc-lem-bc-integral-base`.
(blueprint: lem-sbc-integral-pointed-clopen-refinement)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom.Nbhd

/-- An étale neighbourhood of a point over an integral morphism is refined by a clopen
piece of a base-changed neighbourhood of its image.

Source: blueprint `sbc-lem-bc-integral-base`, proof, the integral algebra over the strict
henselisation and its finite subalgebras.
(blueprint: lem-sbc-integral-pointed-clopen-refinement)

Proof: Shrink the base to an affine neighbourhood. Over its strict henselisation, write the
integral algebra as the filtered union of its finite subalgebras. Shrink the given étale
neighbourhood at the marked point to a standard étale affine. Its finitely many presentation
coefficients descend to one finite subalgebra. A finite algebra over a strictly henselian
local ring is a product of strictly henselian local rings. In the factor selected by the
marked geometric point the descended étale neighbourhood has a section through that point.
Pull back that factor and its complementary factors to the integral algebra. The factor
is clopen and its section gives a map to the original neighbourhood preserving the marked
point. The idempotent defining the factor, its complement, the étale section, and their
finitely many equations descend to a pointed étale neighbourhood of the base geometric
point. This gives P, Q, p and a with the two displayed equalities. No surjectivity of f is
used. If the source is empty there is no geometric point t, so this case is vacuous. -/
theorem exists_pointed_clopen_refinement
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (t : Scheme.Hom.GeometricFiber f y) (V : X.Etale)
    (v : (Scheme.pointSmallEtale t.1).fiber.obj V) :
    ∃ (c : Scheme.Hom.Nbhd y) (P Q : (pullback c.1.hom f).Opens),
      Disjoint P Q ∧ P ⊔ Q = ⊤ ∧
      ∃ (p : (Scheme.pointSmallEtale t.1).fiber.obj (openObj f c P))
        (a : openObj f c P ⟶ V),
        (Scheme.pointSmallEtale t.1).fiber.map a p = v ∧
        (Scheme.pointSmallEtale t.1).fiber.map (openIncl f c P) p =
          ((AlgebraicGeometry.Etale.baseChangeNbhd f y t).obj c).2 := by sorry

end AlgebraicGeometry.Scheme.Hom.Nbhd
