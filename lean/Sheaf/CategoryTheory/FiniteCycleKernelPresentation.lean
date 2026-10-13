/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.DerivedCoupleExact

/-!
# Finite exact-couple quotient kernels

Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2;
Stacks Project, Tags 011R, 011T and 0AMJ.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical finite cycle projection is epic when the following D term is zero,
and its kernel is the inverse image of the next incoming alpha image.

Proof: Recursively construct the image epimorphism e_n from D(p,q) onto
D_n(p-n,q+n). At zero use the identity with the endpoint transport; at a successor
compose e_n with the image epimorphism of the restricted alpha. The canonical
inclusion into original D is mono, and its composite with e_n is alphaIter n,
by the image recurrences and alpha restriction equations of pageCouple_image.
Induction using DerivedMaps.g_comm identifies e_n followed by transported g_n
with the factorization of initialG through Z_n followed by projection n.
At zero use projection_zero. At a successor cancel the monic kernel inclusion
using cycleLift_comm, and then apply projection_succ. Monicity of the cycle
inclusion identifies the resulting lift with the prescribed factorThru.
Exactness gives ker(g_n) as the image of incoming alpha_n. Under the canonical
inclusion of D_n into original D this is the image of the (n+1)-fold incoming
alpha iterate. Taking its inverse image along e_n therefore gives the displayed
pullback along alphaIter n. Finally, the following D object being zero makes
f_n zero; exactness makes g_n epic, hence its composite with e_n is epic.
No half-plane or colimit assumption is used.
Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2, finite image
induction, exact triangle and original-g projection; Stacks Tags 011R and 0AMJ.
(blueprint: lem-sp-finite-cycle-kernel-presentation) -/
theorem finiteCycle_kernel_presentation (X : BigradedExactCouple C 0)
    (r : ℕ) (p q : ℤ)
    (hnext : IsZero ((X.pageCouple r).D (p + 2) (q - 1)))
    (hg : (X.cycleBoundaryTower.Z r p q).Factors (X.initialG p q)) :
    Epi ((X.cycleBoundaryTower.Z r p q).factorThru (X.initialG p q) hg ≫
      X.cycleBoundaryTower.projection r p q) ∧
    kernelSubobject ((X.cycleBoundaryTower.Z r p q).factorThru
        (X.initialG p q) hg ≫ X.cycleBoundaryTower.projection r p q) =
      (Subobject.pullback (X.alphaIter r p q)).obj
        (imageSubobject (X.incomingAlphaIter (r + 1) (p - r) (q + r))) := by sorry

end CategoryTheory.BigradedExactCouple
