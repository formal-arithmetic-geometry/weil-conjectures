module

public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

import Sheaf.Algebra.Homology.KInjectiveProducts
import Sheaf.Algebra.Homology.RoosComplex
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Derived-limit property of a tower limit cone
Source: Stacks Project, Derived Categories, Tags 0BK6, 0BK7 and 070M
(blueprint: lem-weil-derived-limit-tower-core-property). -/

@[expose] public section
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- A limit cone of a represented K-injective tower has the derived-limit property.
This is the Roos comparison part of `derivedCategory_towerLimit_core`.
Source: Stacks Project, Derived Categories, Tags 0BK6, 0BK7 and 070M. Proof:
evaluation at level n has the exact left adjoint which is X through level n
and zero at higher levels. Therefore each evaluated complex is K-injective.
The theorem `termwise_product_isKInjective_and_isLimit` makes their termwise
product represent the derived-category product. The chain map one minus the
shift has the prescribed transition endomorphism after projection to each
factor. Rotate its cone triangle backwards to obtain a derived-limit triangle.
Construct the inverse-limit complex as the degreewise kernel of this chain map;
`roosComplex_quasiIso` identifies it with the shifted cone, including for
K-injective towers whose terms need not be injective or have epi transitions.
Its image under Q is an isomorphism. The uniqueness isomorphism from the supplied
limit cone to this kernel cone transports that triangle to Q(c.pt). Finally e
induces an isomorphism of the products intertwining their transition
endomorphisms. Transport the distinguished triangle along this product
isomorphism to obtain `IsDerivedLimit` for the prescribed tower.
(blueprint: lem-weil-derived-limit-tower-core-property)
-/
theorem derivedCategory_towerLimit_property
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A]
    (hP : HasCountableProducts (DerivedCategory A)) :
    letI : HasCountableProducts (DerivedCategory A) := hP
    ∀ (_ : EnoughInjectives A)
      (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
      (K : ℕ → DerivedCategory A) (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
      (_e : I.asFunctor ⋙ DerivedCategory.Q ≅ Functor.ofOpSequence f)
      (c : Cone I.asFunctor), IsLimit c →
      IsDerivedLimit f (DerivedCategory.Q.obj c.pt) := by
  sorry

end CategoryTheory
