/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.PerfectRingDualTermFlat

/-! # The precomposition term of signed tensor-dual evaluation

Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1),
expanded differential calculation of signed tensor-dual evaluation.
(blueprint: lem-pc-perfect-ring-hom-tensor-precomposition)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency true in
/-- The precomposition term on a single tensor summand and Hom coordinate.
Source: Stacks Project, More on Algebra, Tags 0A6A (1) and 0ATK (1),
expanded differential calculation.
(blueprint: lem-pc-perfect-ring-hom-tensor-precomposition)

Proof: expand the first tensor summand differential as d_D tensor id
followed by the (r+1,s) inclusion, where D=Hom(P,A[0]). If p differs from
-r-1, both sides vanish by the off-diagonal clauses (the original map
is tested at p+1). If p=-r-1, the Hom differential formula for D gives
d_D(lambda)(x)=-(-1)^r lambda(d_P(x)); the postcomposition term is zero
because the differential of A[0] is zero. The degree n+1 normalization
therefore evaluates the left side as
-(-1)^(r+(r+1)*s) lambda(d_P(x)) y. The degree n normalization followed
by precomposition evaluates the right side as
-(-1)^(n+r*s) lambda(d_P(x)) y. Since n=r+s the exponents are equal.
The canonical degree-zero single-complex isomorphism and the Q-degree
transports commute with these evaluations by naturality and proof
irrelevance. Extend the calculation by bilinearity and the sheafification
adjunction, and use evaluation at the unique slice object to detect
equality of internal Hom morphisms. No finite support, projectivity,
or bounds are used. Zero rings and modules and all integer degrees obey
the same calculation. -/
theorem perfectRingHom_tensorDual_precomposition {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory (CochainComplex.onePointRingSheaf A)
    ∀ (a : (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X n ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n)
      (b : (CochainComplex.mapBifunctor (perfectRingDual P) Q (curriedTensor _)).X (n + 1) ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X (n + 1)),
      PerfectRingHomTensorDegreeCondition P Q n a →
      PerfectRingHomTensorDegreeCondition P Q (n + 1) b →
      ∀ (r s p : ℤ) (h : r + s = n),
      HomologicalComplex.mapBifunctor.d₁ (perfectRingDual P) Q (curriedTensor _)
          (ComplexShape.up ℤ) r s (n + 1) ≫ b ≫ ringHomComplexProjection P Q (n + 1) p =
        -n.negOnePow • (CochainComplex.ιMapBifunctor (perfectRingDual P) Q
          (curriedTensor _) r s n h ≫ a ≫
            (homComplex_exists.{u, u, u, u}
              (R := CochainComplex.onePointRingSheaf A)).choose_spec.choose
              P Q n (p + 1) (p + (n + 1)) (by omega) ≫
            SheafOfModules.homObjMap (R := CochainComplex.onePointRingSheaf A)
              (P.d p (p + 1)) (𝟙 (Q.X (p + (n + 1))))) := by sorry

end CategoryTheory
