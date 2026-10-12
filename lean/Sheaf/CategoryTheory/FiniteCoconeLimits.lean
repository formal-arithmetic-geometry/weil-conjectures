module

public import Sheaf.CategoryTheory.ExactCoupleConvergence

/-! Finite diagonal tails yield stationary limiting subobjects.
Source: Stacks Project, Homology, Tag 012W.
(blueprint: lem-sp-finite-cocone-limits).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

/-- Finite diagonal tails make the canonical cycle tower regular and admit limits.
Source: Stacks Project, Homology, Tag 012W.
(blueprint: lem-sp-finite-cocone-limits).

Proof: On each diagonal, the cocone equation and the two eventually
isomorphic structure maps make `Alpha` an isomorphism in a sufficiently
low range. The upper zero tail makes the relevant incoming images eventually
zero. Induction on the derived exact-couple recursion then shows that the
cycle subobjects are eventually constant; the same induction identifies the
boundary subobjects with eventual images of kernels of outgoing iterates.
Decreasing cycles and increasing boundaries therefore have stationary values,
which are their greatest lower and least upper bounds. Taking these values as
the two components of `L` gives a limiting subobject, and cycle stationarity
is exactly the regularity condition. -/
theorem finiteCocone_limits
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (A : ∀ n : ℤ, X.AlphaColimit n)
    (hA : ∀ n : ℤ, ∃ a b : ℤ,
      (∀ P : ℤ, P ≤ a → IsIso ((A n).ι P)) ∧
      (∀ P : ℤ, b ≤ P → IsZero (X.D P (n - P)))) :
    ∃ L : X.LimitSubobjects, X.IsRegular := by sorry

end CategoryTheory.BigradedExactCouple
