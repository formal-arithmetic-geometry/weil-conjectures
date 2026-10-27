/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.RationalStratumPullbackData


/-! # Composition for normalized ambient rational pullback models -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.RationalStratumPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Two normalized ambient pullbacks compose with their actual tensor units.
Source: Stacks 0D6D; Bhatt--Scholze Remark 6.8.15
(blueprint: lem-per-rational-ambient-pull-composition).

Proof: the continuous coefficient adjunct is precomposition. Successive
precomposition agrees with composite precomposition, giving coefficients.
The ordinary comparison inserts the intermediate tensor unit; its inverse
multiplies the two scalar factors. Balancing proves that these maps are inverse.
The unit formula uses the actual fibre-product associator and follows by inserting
one twice. Apply this map termwise to obtain complex and components. Exact inverse
image preserves K-flat complexes, and extension of scalars preserves K-flat complexes
with flat terms. Thus both factorizations compute derived pullback on flat-term
K-flat resolutions. Descend the termwise map through the universal counits. The
normalizations of the supplied counits identify this descended map with the displayed
normalization equation. Uniqueness of left derived functors extends the isomorphism
to arbitrary complexes. These operations apply on arbitrary chart schemes. -/
theorem rational_ambient_pull_composition {X Y Z : Scheme.{u}}
    (g : Y ⟶ X) (h : Z ⟶ Y)
    (cg : (adicTowerInverseImage g).obj (rationalCoefficientSheaf l X E) ⟶
      rationalCoefficientSheaf l Y E)
    (ch : (adicTowerInverseImage h).obj (rationalCoefficientSheaf l Y E) ⟶
      rationalCoefficientSheaf l Z E)
    (hg : rationalCoefficientRestrictionNormalized l E g cg)
    (hh : rationalCoefficientRestrictionNormalized l E h ch)
    (pg : Pull l E g cg) (ph : Pull l E h ch)
    (pc : Pull l E (h ≫ g) (coefficient l E (h ≫ g))) :
    Nonempty (Composition l E g h cg ch pg ph pc) := by sorry

end AlgebraicGeometry.Scheme.RationalStratumPullback
