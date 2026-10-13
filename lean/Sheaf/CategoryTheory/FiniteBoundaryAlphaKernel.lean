/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence

/-! # Finite boundaries as outgoing alpha kernels

Source: Stacks Project, Tag 011T, finite exact-couple boundary formula.
(blueprint: lem-sp-finite-boundary-alpha-kernel)
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

/-- Finite boundaries are the initial g-image of the outgoing iterated alpha kernel.
Source: Stacks Project, Tag 011T, exact-couple boundary formula, and Tag 0AMJ.
(blueprint: lem-sp-finite-boundary-alpha-kernel).

Proof: Induct on r using the canonical tower's successor boundary and projection
formulas. At zero alphaIter is an isomorphism, so its kernel and the tower's
boundary are zero. Recursively compose image projections to obtain an epimorphism
from D(p,q) onto the r-th derived D at (p-r,q+r). The canonical inclusion of
this derived D into the original D is mono and its composite with that epimorphism
is alphaIter r. The derived alpha and g restriction equations imply that the next
alpha kills a representative exactly when alphaIter (r+1) does, and that its g
image equals the projection of initialG of that representative into the r-th page.
Exactness identifies the incoming differential image with derived g of the kernel
of derived alpha. Lift a representative of the successor boundary first through
this image and then through the iterated image epimorphism, after epimorphic
refinements. Its lift is killed by alphaIter (r+1). The difference from its
initialG image has zero projection and hence lies in the old boundary. By induction
that difference is initialG of an element killed by alphaIter r, after refinement.
Adding the two lifts gives an element killed by alphaIter (r+1) representing the
original successor boundary. Conversely an element killed by alphaIter (r+1)
projects to a derived-alpha kernel, so its g image is an incoming differential
boundary; the tower's successor pullback puts its initialG image in B(r+1).
These two factorization tests descend along the epimorphic refinements, since
subobjects in an abelian category are kernels of their cokernels, and prove equality.
The argument uses no colimit, tail, regularity or vanishing hypothesis. -/
theorem finiteBoundary_alphaKernel
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (r : ℕ) (p q : ℤ) :
    X.cycleBoundaryTower.B r p q =
      (Subobject.«exists» (X.initialG p q)).obj (kernelSubobject (X.alphaIter r p q)) := by sorry

end CategoryTheory.BigradedExactCouple
