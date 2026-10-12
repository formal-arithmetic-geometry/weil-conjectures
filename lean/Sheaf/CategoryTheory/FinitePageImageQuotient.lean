/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.DerivedCoupleExact
import Sheaf.CategoryTheory.ExactCouple
import Sheaf.CategoryTheory.Filtration

/-!
# The finite derived-couple quotient in a half-plane

Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2;
Stacks Project, Tags 011R, 011T and 0AMJ.
(blueprint: lem-sp-finite-page-image-quotient)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A finite page whose next D term vanishes is the quotient of consecutive diagonal images,
with the comparison prescribed by the original `g`.

Proof: put `u = p - r` and `v = q + r`. The page index here is `r`, so the
actual spectral-sequence page is `r + 2`. The inequality `p ≤ r` puts `u ≤ 0`.
Exactness makes the diagonal alpha maps at nonpositive first index invertible:
`ker alpha = im f = 0` and `im alpha = ker g = D`, since the two adjacent
initial E objects have negative first index. The cocone equation and the
normalized zeroth map then make the cocone map at `(u,v)` invertible.

Construct epimorphisms `e_n : D(p,q) → D_n(p-n,q+n)` by induction. At zero
use the identity. At a successor, compose `e_n` with the image epimorphism
of `alpha_n(p-n,q+n)` and transport its image to the next derived D term.
Use the iterated inclusion maps of `pageCouple_image`. Their alpha restriction
equations show that the composite of `e_n` with the inclusion into the original
D term is the n-fold diagonal alpha composite. Therefore the cocone equations
identify the mono `D_r(u,v) → D(u,v) → A(p+q)` with the image inclusion of
`ι_p`, because its composite with the epi `e_r` is `ι_p` (with transport).
Apply the same calculation at `(p+1,q-1)` and use the alpha restriction equation:
the image of `alpha_r(u+1,v-1)` in `D_r(u,v)` becomes precisely the next
filtration image `im ι_(p+1)`, included in `im ι_p`.

The D term following E at `(p,q)` is zero by hypothesis, so `f_r(p,q)=0`.
Exactness at E makes the transported `g_r(u,v)` epi, and exactness at D
identifies its kernel with `im alpha_r(u+1,v-1)`. An epi in an abelian category
is the cokernel of its kernel. Thus this E term and the graded piece are
cokernels of the same inclusion, giving their unique comparison isomorphism.

For its projection equation, prove by induction on n that the composite of
`e_n` with transported `g_n` is the cycle lift of the original g followed by
the nth tower projection. At zero this is `projection_zero`. At a successor,
`DerivedMaps.g_comm` rewrites the composite with the next image epimorphism
as `gToCycles` followed by the derived E projection. Cancel the kernel inclusion
to identify its cycle lift with `cycleLift`, using `cycleLift_comm` and the
induction hypothesis. Then `projection_succ` gives exactly the next tower
projection. Every lift of the original g into the nth cycle object is equal
by cancellation of its monic arrow; hence the lift used here equals the
`factorThru` specified by `hg`. At n=r the cokernel comparison equation gives
the displayed equation with `toGradedPiece`.
Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2;
Stacks Project, Tags 011R, 011T and 0AMJ.
(blueprint: lem-sp-finite-page-image-quotient) -/
theorem finitePage_image_quotient (X : BigradedExactCouple C 0)
    (hE : ∀ p q : ℤ, p < 0 → IsZero (X.E p q))
    (A : ∀ n : ℤ, AlphaColimit X n)
    (hA : ∀ n : ℤ, (A n).obj = X.D 0 n)
    (hι : ∀ n : ℤ, (A n).ι 0 ≫ eqToHom (hA n) =
      eqToHom (by congr 1; omega))
    (r : ℕ) (p q : ℤ) (hp : p ≤ (r : ℤ))
    (hnext : IsZero ((X.pageCouple r).D (p + 2) (q - 1)))
    (hg : (X.cycleBoundaryTower.Z r p q).Factors (X.initialG p q)) :
    ∃ e : (X.pageCouple r).E p q ≅
      (X.imageFiltration (p + q) (A (p + q))).gradedPiece p,
      (X.cycleBoundaryTower.Z r p q).factorThru (X.initialG p q) hg ≫
        X.cycleBoundaryTower.projection r p q ≫ e.hom = X.toGradedPiece A p q := by
  sorry

end CategoryTheory.BigradedExactCouple
