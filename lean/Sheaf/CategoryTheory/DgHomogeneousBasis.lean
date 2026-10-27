module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import Mathlib.Data.DFinsupp.Defs

/-!
# Homogeneous bases of graded right DG modules

Source: Stacks Project, dga.tex, Tag 0CRM, lemma-countable, the homogeneous generators
chosen from the graded splittings of property (P); Tag 09KP, lemma-resolve
(blueprint: def-sfb-dg-homogeneous-basis).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoryTheory.DgAlgebra

open Classical in
/-- A homogeneous free right graded basis, with the actual right action. In degree `n`
its coordinates are finitely supported coefficients in `A^(n-degree j)`. The equation
`coordinate_generator` says the inverse of a single coordinate is the corresponding
basis vector multiplied on the right by that coefficient. It therefore specifies the
free graded right module, rather than just an additive decomposition. No compatibility
with the differential is imposed on the generators.
Source: Stacks Project, dga.tex, Tag 0CRM, lemma-countable, homogeneous generators from
property (P); Tag 09KP, lemma-resolve (blueprint: def-sfb-dg-homogeneous-basis). -/
structure HomogeneousBasis (A : Algebra.{u}) (P : RightModule A) where
  Index : Type u
  degree : Index → ℤ
  generator (j : Index) : ((underlying A).obj P).X (degree j)
  coordinate (n : ℤ) : ((underlying A).obj P).X n ≃+
    (Π₀ j : Index, A.X.X (n - degree j))
  coordinate_generator (j : Index) (n : ℤ) (a : A.X.X (n - degree j)) :
    coordinate n
      ((((underlying A).obj P).XIsoOfEq (by omega : degree j + (n - degree j) = n)).hom
        (act A P (degree j) (n - degree j) (generator j) a)) = DFinsupp.single j a

end CategoryTheory.DgAlgebra
