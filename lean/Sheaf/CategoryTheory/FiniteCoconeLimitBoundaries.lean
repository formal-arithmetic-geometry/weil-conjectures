/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence

/-! # Finite-tail limiting subobjects

Source: Stacks Project, Tag 011T, exact-couple cycle and boundary formulas.
(blueprint: lem-sp-finite-cocone-limit-boundaries)
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

/-- An invertible left cocone tail identifies limiting boundaries with g of its kernel.
Source: Stacks Project, Tag 011T, formula for boundaries; Tag 012W, lower-tail argument.
(blueprint: lem-sp-finite-cocone-limit-boundaries).

Proof: Write T for the canonical cycle-boundary tower, and suppress only the
canonical integer-index transports. First prove by induction on r that
T.B r p q = initialG(ker(alphaIter r p q)). At r=0 the iterate is an
isomorphism and T.B 0 is zero. For the induction, construct the canonical epi
 e_r : D(p,q) -> D_r(p-r,q+r) by iterating image projections. Its composite
with the canonical mono inclusion I_r is alphaIter r. The derived-map
restriction equations show that e_r followed by derived g_r agrees with the
factorization of initialG into T.Z r followed by T.projection r. They also
show that derived alpha_r followed by the next I_r agrees with the original
alpha at the endpoint of alphaIter r. Hence e_r(x) is killed by derived alpha
exactly when x is killed by alphaIter (r+1), by monicity of I_r.

Use generalized elements with epimorphic refinements throughout. Exactness
of the r-th couple identifies the incoming differential image at (p,q) with
derived g_r of ker(derived alpha_r) at (p-r,q+r). Given an element z of the
pullback defining T.B (r+1), lift its differential-image representative to
ker(derived alpha_r), then lift along e_r after refinement. The lift x is
killed by alphaIter (r+1). The projection of z-initialG(x) is zero, so this
difference lies in T.B r by projection_kernel. By induction it is initialG(y)
for y killed by alphaIter r, after another refinement. Thus z=initialG(x+y),
with x+y killed by alphaIter (r+1). Conversely, any such x maps under e_r
into ker(derived alpha_r)=im(derived f_r); its derived g image is an incoming
differential boundary. Since initialG(x) lies in all cycles, B_succ places it
in T.B (r+1). These tests prove the induction equality. Refinements descend
because each subobject is the kernel of its cokernel in an abelian category.

Let j_p be the transported cocone map in the conclusion. Iterating A.comm
shows j_p = alphaIter r p q followed by the transported map A(p+q).ι(p-r).
Choose a from hleft(p+q). For every r with p-r <= a the second factor is an
isomorphism, so ker(alphaIter r p q)=ker(j_p). For every smaller r, its kernel
is contained in ker(j_p) by the same cocone equation. Thus all T.B r are at
most initialG(ker(j_p)), and all sufficiently large r equal it. This value
is the least upper bound of the boundary range; uniqueness with L.B_lub
proves the assertion. No cycle regularity or upper zero tail is needed. -/
theorem finiteCocone_limitBoundaries
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (A : ∀ n : ℤ, X.AlphaColimit n)
    (hleft : ∀ n : ℤ, ∃ a : ℤ, ∀ P : ℤ, P ≤ a → IsIso ((A n).ι P))
    (L : X.LimitSubobjects) (p q : ℤ) :
    L.B p q = (Subobject.«exists» (X.initialG p q)).obj
      (kernelSubobject (eqToHom (by congr 1; omega) ≫ (A (p + q)).ι p)) := by sorry

end CategoryTheory.BigradedExactCouple
