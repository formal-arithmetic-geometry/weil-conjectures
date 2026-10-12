module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

@[expose] public section
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- The image of the termwise product cone is limiting, without assuming that products
already exist in the derived category.
Source: Stacks Project, Derived Categories, Lemma 13.34.2 (Tag 07KC).

Proof: work first in the homotopy category, where termwise products are products:
chain maps and their homotopies into a product are given componentwise. Exact countable
products commute with homology, so a product of quasi-isomorphisms is a quasi-isomorphism.
For any complex L, represent each morphism from Q(L) to Q(C j) by a left fraction
L → M j ← C j. The product of the denominators is a quasi-isomorphism and the maps
from L assemble into a map to the product of the M j. This fraction is a lift of the
given family. For uniqueness, represent the difference of two lifts by a fraction
L → N ← ∏ C j. For each j, apply the left Ore condition to its denominator and the
projection ∏ C j → C j to obtain a fraction for the j-th component. Since that
component is zero, the equality criterion for fractions gives a further denominator
killing its numerator in the homotopy category. Thus there are maps a j : N → M' j
and quasi-isomorphisms t j : C j → M' j with s ≫ a j = π j ≫ t j and f ≫ a j = 0.
Assemble a : N → ∏ M' j. Then s ≫ a is the product of the t j, hence a
quasi-isomorphism. Since s is a quasi-isomorphism, so is a, by two-out-of-three.
All components of f ≫ a vanish; the product universal property makes f ≫ a = 0.
As a is inverted in the localization, the difference is zero there. Every derived object
is isomorphic to Q(L), so this proves the universal
property for all vertices. Empty and singleton families give the zero and identity
cones, respectively.
(blueprint: lem-weil-derived-countable-products-core) -/
theorem derivedCategory_termwiseProduct_isLimit
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A]
    (J : Type) [Countable J] (C : J → CochainComplex A ℤ) :
    Nonempty (IsLimit (DerivedCategory.Q.mapCone (limit.cone (Discrete.functor C)))) := by
  sorry

end CategoryTheory
