module

public import Sheaf.CategoryTheory.ExactCoupleConvergence

/-! Canonical weak-convergence maps for a finite diagonal exact couple.
Source: Stacks Project, Homology, Tag 012W.
(blueprint: lem-sp-finite-cocone-weak-maps).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

/-- Under finite diagonal tails, any regular limiting tower has the canonical weak convergence.
Source: Stacks Project, Homology, Tag 012W.
(blueprint: lem-sp-finite-cocone-weak-maps).

Proof: Use the stationary cycle and boundary descriptions from the derived
exact-couple recursion. Exactness identifies stationary cycles with the image
of the initial `g`, so the canonical map from `D` onto the limiting quotient
is epi. Its kernel is the sum of the image of `Alpha` and the kernel of the
diagonal cocone map. The canonical map to the graded image of the cocone is
also epi by image factorisation. Pulling the next cocone image back along the
current map gives the same sum by the cocone equation and abelian
image/kernel calculus; exactness identifies the image of `Alpha` with the
kernel of `g`. Thus the two canonical epimorphisms have equal kernels, which
is precisely `WeaklyConvergesTo`. -/
theorem finiteCocone_weakMaps
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (A : ∀ n : ℤ, X.AlphaColimit n)
    (hA : ∀ n : ℤ, ∃ a b : ℤ,
      (∀ P : ℤ, P ≤ a → IsIso ((A n).ι P)) ∧
      (∀ P : ℤ, b ≤ P → IsZero (X.D P (n - P))))
    (L : X.LimitSubobjects) (hreg : X.IsRegular) : X.WeaklyConvergesTo L A := by sorry

end CategoryTheory.BigradedExactCouple
