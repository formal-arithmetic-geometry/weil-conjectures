/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointWeilPairingCoordinates

/-! # Transport of ordered shifted tensor representatives

Source: retained rational point-pairing argument.
(blueprint: lem-pod-point-weil-tensor-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointWeilPairing
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Pullback transports the coefficient diagonal and the tensor of two representatives.
Source: retained point-pairing proof Steps 3--5, before application of B.
(blueprint: lem-pod-point-weil-tensor-representatives).
Proof: the canonical pullback tensor comparison is natural and unital. Its unit
comparison is c: the finite coefficient unit is multiplication after kappa,
and lambda kappa = id identifies it with the canonical coefficient Weil map;
the integral projection formulas and rational localization preserve this equality.
Apply its unit coherence to the inverse unitor j and cancel c to obtain the
first equation. For the second, expand pairingVector. Move the shifted theta
maps through the signed tensor-shift comparison by naturality. The pullback
tensor square replaces the tensor of P(x) and P(y) by P of their tensor,
conjugated by mu. The total-complex shift has coefficient (-1)^(j*p), which
is preserved by pullback since degrees and scalars are unchanged. The completed
comparison uses the same product and cone shift on both paths, so this square
survives completion and rationalization. Shift addition and shift zero are
natural and commute with the fixed pullback shift. Finally replace the two
inverse coefficient maps using the first equation. This gives exactly the
second displayed composite. No pairing B or Weil equation is used, and no
permutation of the two inputs occurs. All shifts, including negative ones,
and zero objects satisfy these identities. -/
theorem point_weil_tensor_representatives :
    ((c D l hl E).inv ≫ (P D l hl E).map (j D l hl E) ≫
        (mu D l hl E (U D l hl E) (U D l hl E)).hom =
      j D l hl E ≫ (T D l hl E).map
        (Prod.mkHom (c D l hl E).inv (c D l hl E).inv)) ∧
    (∀ (A D₁ : C D l E) (thetaA : (P D l hl E).obj A ≅ A)
      (thetaD : (P D l hl E).obj D₁ ≅ D₁) (n i : ℤ)
      (x : U D l hl E ⟶ A⟦i⟧) (y : U D l hl E ⟶ D₁⟦n - i⟧),
      pairingVector D l hl E A D₁ n i
          (frobeniusRep D l hl E A thetaA i x)
          (frobeniusRep D l hl E D₁ thetaD (n - i) y) =
        (c D l hl E).inv ≫ (P D l hl E).map (pairingVector D l hl E A D₁ n i x y) ≫
          (mu D l hl E A (D₁⟦n⟧)).hom ≫
          (T D l hl E).map
            (Prod.mkHom thetaA.hom (shiftedTheta D l hl E D₁ thetaD n).hom)) := by
  sorry

end WeilConjectures.PointWeilPairing
