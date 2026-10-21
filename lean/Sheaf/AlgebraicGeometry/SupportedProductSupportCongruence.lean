/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P9
-/
module

public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
public import Sheaf.AlgebraicGeometry.NormalizedSupportTriangle

/-! # Invariance of the supported product under equal closed supports

Source: blueprint supported exterior product, quotient normalization, and Tag 09XP.
(blueprint: lem-pur-supported-product-support-congruence).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

/-- Invertibility of the supported exterior product depends only on the closed supports,
not their scheme structures or their presentations as closed immersions.
Source: blueprint `def-pur-supported-exterior-product`, quotient normalization;
Tag 09XP, invariance of supported sections under equality of closed subsets.
(blueprint: lem-pur-supported-product-support-congruence).

Proof: the equal open complements identify the two kernels defining supported sections
and their inclusions into global sections. The normalized coefficient adjunctions have
these same right adjoints, so uniqueness of left adjoints identifies their left adjoints.
The identification commutes with the quotient from constant coefficients, by the defining
normalization of the Hom bijections. Precompose the two coefficient tensor comparisons
with the quotient of constant tensor sections: both give the constant tensor pairing and
the two pulled-back quotients. The quotient is epic, so the comparisons agree under these
identifications. The signed total-complex comparisons agree on every bidegree summand;
uniqueness of their derived comparison families gives the same equality after localization.
The evaluation counits commute with the adjoint identifications. Transposing their tensor
therefore identifies the two supported products, conjugated by isomorphisms of supported
sections on the source and product. Conjugation preserves and reflects invertibility.
This argument includes empty and full supports and uses no boundedness assumption.
-/
theorem isIso_supportedExteriorProduct_iff_supportComplement_eq
    (A : Type (u + 1)) [CommRing A] {S X Y Z Z' W W' : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ X) (i' : Z' ⟶ X)
    (j : W ⟶ Y) (j' : W' ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion i']
    [IsClosedImmersion j] [IsClosedImmersion j']
    (hi : i.openComplement = i'.openComplement)
    (hj : j.openComplement = j'.openComplement)
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    IsIso (supportedExteriorProduct A f g i j K L) ↔
      IsIso (supportedExteriorProduct A f g i' j' K L) := by sorry

end AlgebraicGeometry.Etale
