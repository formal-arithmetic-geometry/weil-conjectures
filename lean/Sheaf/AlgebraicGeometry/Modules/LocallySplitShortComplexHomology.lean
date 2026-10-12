/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeComplex
import Sheaf.RingTheory.FiniteProjectiveStandardFreeCover
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Homology of a short complex with locally split boundaries

Source: `thm-pc-semicontinuity-base-change`, proof (3), kernel/image splitting argument.
(blueprint: lem-pc-locally-split-short-complex-homology)
-/

@[expose] public section

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- If the outgoing kernel and the incoming image are finite locally free, and the
incoming image is locally a direct summand of the middle term, homology is finite
locally free of the difference of their ranks.

Source: `thm-pc-semicontinuity-base-change`, proof (3), kernel/image splitting argument.
(blueprint: lem-pc-locally-split-short-complex-homology)

Proof: Around each point take an affine neighbourhood where the image inclusion admits
its given retraction and both kernel and image are free of their stated finite ranks.
The short-complex identity factors the image inclusion through the outgoing kernel.
Restricting the retraction to that kernel splits the image inclusion into the kernel.
On affine sections the quotient of the kernel by the image is therefore a direct
summand of a finite free module, hence finite projective. The finite standard free cover
for a finite projective module gives smaller principal opens on which this quotient is
free. After passage to any residue field the split exact sequence of image, kernel and
quotient remains exact; dimension additivity gives b <= k and quotient rank k-b.
The affine equivalence for quasi-coherent modules is exact, and homology is the cokernel
of the image-to-kernel map. Thus the sheaf associated to this quotient is the short
complex's homology. Open restriction is exact and preserves homology, so the local
identifications are of the restrictions of that homology sheaf. The refined opens cover
the scheme, proving finite local freeness of rank k-b. On an empty scheme there are no
points to cover and the assertion is vacuous; the zero-rank cases use zero free modules.
No reducedness or freeness of the terms of the short complex is required. -/
theorem isFiniteLocallyFreeOfRank_homology_of_locally_split_image
    {Z : Scheme.{u}} (S : ShortComplex Z.Modules) (k b : ℕ)
    (hkernel : (kernel S.g).IsFiniteLocallyFreeOfRank k)
    (himage : (Abelian.image S.f).IsFiniteLocallyFreeOfRank b)
    (hsplit : ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
      IsSplitMono ((restrictFunctor U.ι).map (Abelian.image.ι S.f))) :
    S.homology.IsFiniteLocallyFreeOfRank (k - b) := by sorry

end AlgebraicGeometry.Scheme.Modules
