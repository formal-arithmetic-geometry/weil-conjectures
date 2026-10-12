module

public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Functor

import Sheaf.Algebra.Homology.KInjectiveProducts
import Sheaf.Algebra.Homology.RoosComplex
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

@[expose] public section
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- The inverse limit of a K-injective tower represents its triangulated derived limit.
Source: Stacks Project, Derived Categories, Tags 0BK6, 0BK7 and 070M, together with
clause (3) of the blueprint lem-weil-derived-limit-existence
(blueprint: lem-weil-derived-limit-tower-core).

Proof: Evaluation at n has the exact left adjoint which is X through level n and zero
above n. Therefore evaluation preserves K-injectivity. The termwise product P of the
evaluated complexes is K-injective and its image under Q, with the projected maps, is the
derived-category product (termwise_product_isKInjective_and_isLimit). Form the chain map
1-s on P. The cone triangle rotated backwards identifies its shifted cone with a derived
limit. Construct L degreewise as the kernel of 1-s; its projections form the limit cone
of the tower, because kernels and products compute inverse limits in an additive category
and limits of complexes are degreewise. The canonical map from L to the shifted cone is
a quasi-isomorphism by roosComplex_quasiIso. That result applies to arbitrary K-injective
towers via a split-envelope replacement and a homotopy retraction; it does not require
the terms of I to be injective or the transitions to be epimorphisms. Its image under Q
is an isomorphism, so transport the distinguished triangle to Q(L). Finally the given
natural isomorphism e identifies each projection and transition with the prescribed
(K,f), and the induced product isomorphism transports the triangle to that tower. -/
theorem derivedCategory_towerLimit_core
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A]
    (hP : HasCountableProducts (DerivedCategory A)) :
    letI : HasCountableProducts (DerivedCategory A) := hP
    ∀ (_ : EnoughInjectives A)
      (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
      (K : ℕ → DerivedCategory A) (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
      (_e : I.asFunctor ⋙ DerivedCategory.Q ≅ Functor.ofOpSequence f),
      ∃ c : Cone I.asFunctor, Nonempty (IsLimit c) ∧
        IsDerivedLimit f (DerivedCategory.Q.obj c.pt) := by
  sorry

end CategoryTheory
