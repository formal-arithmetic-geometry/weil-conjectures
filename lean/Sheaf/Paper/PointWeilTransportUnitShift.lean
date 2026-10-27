/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointWeilPairingCoordinates

/-! # Unit and shift normalization of point transport

Source: retained rational point-pairing argument.
(blueprint: lem-pod-point-weil-transport-unit-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] AlgebraicGeometry.Scheme.residueLisseAlgebraHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointWeilPairing
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Normalize geometric transport on the unit, shifted Hom classes, and scalars.
Source: retained point-pairing proof Steps 2, 3 and 6.
(blueprint: lem-pod-point-weil-transport-unit-shift).
Proof: restriction and the inverse-image coprojection send the constant section 1
 to 1. The canonical coefficient comparison sends it to 1 tensor 1, with zero
second cone coordinate integrally. The coefficient pullback reduction identity
lambda kappa = id cancels these comparisons against c at exponent zero. Thus
F(c) iota_U is the identity. Apply naturality of point transport to x from U.
On shifts the Roos comparison is (b,a) mapping to ((-1)^r b,a), so the zero
cone coordinate stays zero; the termwise inverse-image maps commute with the
shifted differential. Localize this shift square and use the uniquely normalized
fibre shift. Evaluation at 1 gives the asserted transportRep identity.
Finally full faithfulness and the projective-single Hom equivalence identify
every endomorphism of U with a unique E scalar. Pullback is E-linear on the
rational Hom tensor groups, so conjugating its image by c fixes that scalar,
and therefore the endomorphism itself. The argument applies to all integer
shifts and rational morphisms and uses no Frobenius-stable lattice. -/
theorem point_weil_transport_unit_shift :
    frobenius D l hl E (U D l hl E) (c D l hl E) = 𝟙 _ ∧
    (∀ (N : C D l E) (r : ℤ) (x : U D l hl E ⟶ N⟦r⟧),
      realize D l hl E ((P D l hl E).obj N) r (transportRep D l hl E N r x) =
        (DerivedCategory.homologyFunctor.{u} (ModuleCat.{u} E) r).map
          (iota D l hl E N) (realize D l hl E N r x)) ∧
    (∀ h : U D l hl E ⟶ U D l hl E,
      (c D l hl E).inv ≫ (P D l hl E).map h ≫ (c D l hl E).hom = h) := by
  sorry

end WeilConjectures.PointWeilPairing
