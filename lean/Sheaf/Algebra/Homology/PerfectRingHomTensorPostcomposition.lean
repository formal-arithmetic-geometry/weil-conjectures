/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees

/-! # The postcomposition term of signed tensor-dual evaluation

Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1),
expanded differential calculation of signed tensor-dual evaluation.
(blueprint: lem-pc-perfect-ring-hom-tensor-postcomposition)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency true in
/-- The postcomposition term on a single tensor summand and Hom coordinate.
Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1),
expanded differential calculation.
(blueprint: lem-pc-perfect-ring-hom-tensor-postcomposition)

Proof: expand the second tensor summand differential as (-1)^r times
id tensor d_Q followed by the (r,s+1) inclusion. If p differs from -r,
both sides vanish by the off-diagonal clause of the two degree conditions.
If p=-r, test on lambda tensor y and x. Naturality of the tensor
sheafification comparison gives (-1)^r lambda tensor d_Q(y). The degree
n+1 condition evaluates this as (-1)^r (-1)^(r*(s+1)) lambda(x) d_Q(y).
The degree n condition followed by postcomposition gives
(-1)^(r*s) d_Q(lambda(x) y). Linearity of d_Q and the identity
(-1)^r (-1)^(r*(s+1)) = (-1)^(r*s) give equality. The equation
s=-r+n identifies the target degrees; naturality of eqToHom identifies
the transported differentials. Extend from pure tensors by the tensor
universal property, then use the sheafification adjunction and equality
on the unique slice object to recover the sheaf morphisms. No finite
support, projectivity, or bounds are used. The same equations hold over
the zero ring, for zero modules, and for negative degrees. -/
theorem perfectRingHom_tensorDual_postcomposition {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ∀ (a : (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n)
      (b : (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X (n + 1) ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X (n + 1)),
      PerfectRingHomTensorDegreeCondition P Q n a →
      PerfectRingHomTensorDegreeCondition P Q (n + 1) b →
      ∀ (r s p : ℤ) (h : r + s = n),
      HomologicalComplex.mapBifunctor.d₂ (perfectRingDual P) Q (curriedTensor _)
          (ComplexShape.up ℤ) r s (n + 1) ≫ b ≫ ringHomComplexProjection P Q (n + 1) p =
        CochainComplex.ιMapBifunctor (perfectRingDual P) Q (curriedTensor _)
          r s n h ≫ a ≫ ringHomComplexProjection P Q n p ≫
            SheafOfModules.homObjMap (R := CochainComplex.onePointRingSheaf A)
              (𝟙 (P.X p)) (Q.d (p + n) (p + (n + 1))) := by sorry

end CategoryTheory
