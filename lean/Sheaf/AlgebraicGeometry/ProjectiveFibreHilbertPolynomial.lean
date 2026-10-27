/-
Copyright (c) 2026 SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Numerical polynomials and the fibre polynomial of a projective closed family

Source: Grothendieck, Bourbaki Expose 221, Section 3, pp.259--266; Stacks Project,
Tag 0B9T. The eventual Euler polynomial is the numerical Hilbert polynomial of the
homogeneous coordinate ring: Serre vanishing and the eventual identification of graded
coordinates with sections give the same eventual function. Residue-field extension leaves
these finite-dimensional cohomology groups unchanged in dimension.
(blueprint: def-sfb-projective-fibre-hilbert-polynomial)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A rational numerical polynomial takes integer values at every integer. No positivity
or realizability is imposed; an unrealizable polynomial indexes an empty Hilbert component.
Source: Grothendieck, Bourbaki Expose 221, Section 3, numerical-polynomial indexing.
(blueprint: def-sfb-projective-fibre-hilbert-polynomial) -/
def NumericalHilbertPolynomial : Type :=
  { P : Polynomial ℚ // ∀ m : ℤ, ∃ z : ℤ, P.eval (m : ℚ) = (z : ℚ) }

/-- Every fibre of the closed family has numerical Hilbert polynomial `P`, for the
polarization induced by `i`. The base of the ambient projective space may differ from the
family base, allowing the same polarization to be used after arbitrary base change.
On the projective fibres in question, the eventual Euler characteristic of these twists
is exactly the eventual dimension of the degree-m homogeneous coordinate ring. No choice of
polynomial, homogeneous ideal, or algebraic closure is made here.
Source: Grothendieck, Bourbaki Expose 221, Section 3; Stacks Project, Tag 0B9T.
(blueprint: def-sfb-projective-fibre-hilbert-polynomial) -/
def HasProjectiveFibreHilbertPolynomial {W B S : Scheme.{u}} {n : ℕ}
    (f : W ⟶ B) (i : W ⟶ ℙ(ULift.{u} (Fin (n + 1)); S)) (T : Over B)
    (I : (pullback f T.hom).IdealSheafData) (P : Polynomial ℚ) : Prop :=
  ∀ t : T.left, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    P.eval (m : ℚ) =
      (((Scheme.Modules.tensorPullback
        (I.subschemeι ≫ pullback.fst f T.hom ≫ i)).obj
          (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) S (m : ℤ))).eulerCharFiber
          (I.subschemeι ≫ pullback.snd f T.hom) t : ℚ)

end AlgebraicGeometry
