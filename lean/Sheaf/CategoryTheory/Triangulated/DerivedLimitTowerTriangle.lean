module

public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

import Sheaf.Algebra.Homology.KInjectiveProducts
import Sheaf.Algebra.Homology.RoosComplex
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

@[expose] public section
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- The localized evaluation tower of a K-injective complex has a Roos triangle.
Source: Stacks Project, Derived Categories, Tags 0BK6, 0BK7 and 070M, with the
arbitrary K-injective tower extension proved by `roosComplex_quasiIso`.

Proof: Evaluation at n is right adjoint to the exact functor sending X to the
inverse system which is X at levels at most n and zero above n, with identity
transitions between nonzero terms. Thus evaluation preserves K-injective
complexes by `Adjunction.preservesKInjectiveComplexes`. Form the termwise
product P of these evaluated complexes. By
`termwise_product_isKInjective_and_isLimit`, Q(P), with its localized
projections, is their product in the derived category. Define s by its
components pr(n+1) followed by the transition to level n, and set t = 1-s.
The differential commutes with t by naturality of the tower's differentials.
The cone c identifies degreewise with the kernel of t: compatible families
are precisely the families killed by 1-s, and evaluation preserves limits
of complexes. Construct the shifted cone of t. The canonical map from this
kernel to the shifted cone is a quasi-isomorphism by `roosComplex_quasiIso`;
this applies to K-injective complexes of towers without assuming their
terms are injective or their transitions are epimorphisms. Localizing the
backwards rotated cone triangle gives a distinguished triangle starting at
Q(c.pt). The product isomorphism Q(P) to the chosen product intertwines t
with `towerTransitionEndomorphism`, as checked on each projection. Transport
along this isomorphism gives the asserted triangle, whose first map is the
product lift of the localized legs of c. No representation of a
second tower is used here; that transport is proved by the caller.
(blueprint: lem-weil-derived-limit-tower-core-property-triangle)
-/
theorem derivedCategory_towerLimit_triangle
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A]
    (hP : HasCountableProducts (DerivedCategory A)) :
    letI : HasCountableProducts (DerivedCategory A) := hP
    ∀ (_ : EnoughInjectives A)
      (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
      (c : Cone I.asFunctor), IsLimit c →
      let K₀ := fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (Opposite.op n))
      let f₀ := fun n : ℕ ↦ DerivedCategory.Q.map
        (I.asFunctor.map (homOfLE (Nat.le_succ n)).op)
      let p := Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map (c.π.app (Opposite.op n)))
      ∃ δ : (∏ᶜ K₀) ⟶ (DerivedCategory.Q.obj c.pt)⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle f₀ (DerivedCategory.Q.obj c.pt) p δ := by
  sorry

end CategoryTheory
