module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

import Sheaf.Algebra.Homology.RoosComplex

@[expose] public section
universe w v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- A Roos triangle with the localized product complex as its middle objects.
Source: Stacks Project, Derived Categories, Tags 0BK7 and 070M, using the
arbitrary K-injective tower extension `roosComplex_quasiIso`.

Proof: Evaluation preserves limits of complexes, so the limit cone c and the
product fan P remain limiting in each degree. The projection equations for t
identify its degree-p component with one minus the transition shift, under the
unique isomorphism from P.pt.X p to the chosen product of (I.X p). The equations
for iota identify c.pt.X p with the kernel of that component: the kernel equation
is the compatibility equation for an inverse-limit family, and its universal
property follows by lifting such a family through c. Construct the shifted
mapping cone of t, with terms P.pt.X (p-1) biproduct P.pt.X p and differential
(-d x - t y, d y). The kernel-cone comparison has components (0, iota).
Apply `roosComplex_quasiIso` with these degreewise product isomorphisms, kernel
forks and cone isomorphisms; the comparison localizes to an isomorphism. Localize
the mapping-cone triangle and rotate it backwards. Its first map, after the
comparison isomorphism and the conventional sign isomorphism of the first
object, is Q(iota), and its second map is Q(t). Transport the distinguished
triangle along these isomorphisms. Its third map supplies delta.
This step neither proves that Q(P.pt) is a derived-category product nor uses
chosen products in the derived category; the caller proves and applies that
separate fact.
(blueprint: lem-weil-derived-limit-tower-roos-triangle)
-/
theorem derivedCategory_tower_roos_triangle
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A] [EnoughInjectives A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective]
    (c : Cone I.asFunctor) (hc : IsLimit c)
    (P : Fan (fun n : ℕ ↦ I.asFunctor.obj (Opposite.op n))) (hP : IsLimit P)
    (iota : c.pt ⟶ P.pt) (t : P.pt ⟶ P.pt)
    (hiota : ∀ n : ℕ, iota ≫ P.proj n = c.π.app (Opposite.op n))
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj n -
      P.proj (n + 1) ≫ I.asFunctor.map (homOfLE (Nat.le_succ n)).op) :
    ∃ δ : DerivedCategory.Q.obj P.pt ⟶ (DerivedCategory.Q.obj c.pt)⟦(1 : ℤ)⟧,
      Pretriangulated.Triangle.mk (DerivedCategory.Q.map iota)
        (DerivedCategory.Q.map t) δ ∈ distTriang (DerivedCategory A) := by
  sorry

end CategoryTheory
