/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.DerivedCoupleExact
import Sheaf.CategoryTheory.ExactCouple
import Sheaf.CategoryTheory.Filtration

/-!
# Canonical quotient maps in half-plane convergence

Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2, canonical comparison.
(blueprint: lem-sp-half-plane-weak-convergence)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- For any limiting subobjects and normalized diagonal colimits, the two canonical
maps to the infinite page and the filtration graded piece are epimorphic with equal kernels.

Proof: fix `(p,q)`. Choose a page number `R` larger than both differential bounds
and with `u = p - R + 2 ≤ 0`, and put `v = q + R - 2`. The cycle/boundary recursion
is stationary from this page onwards, since the incoming source has negative first
index and the outgoing target has second index below `a`. Hence the greatest lower
bound of the cycles and least upper bound of the boundaries are those stationary
values; the infinite page is their quotient and canonically identifies with `E_R`.
Iterated derived-couple exactness identifies `D_R` with the incoming alpha images.
Along total degree `p+q`, the negative first-index transitions are invertible.
The normalization at first index zero and the cocone equations therefore identify
`D_R^{u,v}` with the image of `D^{p,q}` in the diagonal colimit, and the incoming
alpha image with the next filtration step. The next D term in the exact triangle
is the image of a map from `D^{p+R,q-R+1}` and vanishes by the D bound.
Thus the map from the first image to `E_R^{p,q}` is a cokernel of the next image.
The derived-g restriction equation, iterated R-2 times, identifies the composite
from `D^{p,q}` with the quotient of the original `g`. This is exactly the map
`toPageInfinity`, by the successor projection equation of the cycle tower.
The map `toGradedPiece` is the other cokernel of the same inclusion, precomposed
with the same epimorphism onto the image. Both maps are therefore epimorphic and
have the same kernel. For `p < 0`, the initial E term and all its subquotients
vanish; the two consecutive filtration steps are the whole colimit, so both
quotient targets are zero and the same assertion holds. This argument also
covers `q < a`, when the source D is zero.
Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2;
Stacks Project, Tags 011T and 012F.
(blueprint: lem-sp-half-plane-weak-convergence) -/
theorem halfPlane_weak_convergence (X : BigradedExactCouple C 0) (a : ℤ)
    (hD : ∀ p q : ℤ, q < a → IsZero (X.D p q))
    (hE : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q))
    (L : LimitSubobjects X) (A : ∀ n : ℤ, AlphaColimit X n)
    (hA : ∀ n : ℤ, (A n).obj = X.D 0 n)
    (hι : ∀ n : ℤ, (A n).ι 0 ≫ eqToHom (hA n) =
      eqToHom (by congr 1; omega)) : X.WeaklyConvergesTo L A := by
  sorry

end CategoryTheory.BigradedExactCouple
