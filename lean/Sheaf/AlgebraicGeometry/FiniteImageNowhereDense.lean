/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.GDelta.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.FiniteAffineSectionCover
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Finite images of closed nowhere dense subsets

Source: Stacks Project, Morphisms, Tag 03HX, Lemma `lemma-image-nowhere-dense-finite`
(blueprint: lem-sfb-finite-image-nowhere-dense).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite morphism sends a closed nowhere dense subset to a closed nowhere dense subset.
Source: Stacks Project, Morphisms, Tag 03HX, Lemma `lemma-image-nowhere-dense-finite`
(blueprint: lem-sfb-finite-image-nowhere-dense).

Proof:
1. By `lem-weil-pbc-finite-closed-map-finite-fibres`, the image is closed. Restrict to an
   affine open cover of the target, using `lem-weil-pbc-finite-morphism-permanence` for
   finiteness of the restrictions. The intersections of `T` with these inverse images
   are still closed and nowhere dense, so it suffices to treat an affine target.
2. Apply `lem-weil-pbc-finite-affine-section-cover` to get a surjective finite locally
   free base change `b : X' ⟶ X`, the projection `a : Y' ⟶ Y`, and a closed immersion
   `j : Y' ⟶ W` over `X'`. The finite locally free map `q : W ⟶ X'` has a finite closed
   section cover, and `j ≫ q` is the base-changed map `f'`.
3. By `def-pc-finite-locally-free` and `lem-weil-pbc-flat-lfp-open`, `a` and `b` are open.
   Thus `T' = a⁻¹(T)` is closed nowhere dense: an open contained in it has open image
   contained in `T`, hence is empty. By `def-weil-closed-immersion`, `j` is a closed
   embedding, so `A = j(T')` is closed nowhere dense in `W`: an open contained in `A`
   pulls back to an open contained in `T'`, hence is empty.
4. Apply `lem-sfb-nowhere-dense-section-cover-image` to `q` and `A` to see that
   `q(A) = f'(T')` is closed nowhere dense in `X'`.
5. By `lem-weil-pbc-base-change-image`, `f'(T') = b⁻¹(f(T))`. Any open in `X` contained
   in `f(T)` has empty inverse image under `b`, and hence is empty by surjectivity.
   Since `f(T)` is closed, it is nowhere dense on the affine target.
6. On the original affine cover, every intersection of an open contained in `f(T)`
   with a member of the cover is empty. The open itself is therefore empty, proving
   the global nowhere-density assertion, together with closedness from step 1. -/
theorem Scheme.Hom.isClosed_isNowhereDense_image_of_isFinite
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    (T : Set Y) (hT : IsClosed T) (hnow : IsNowhereDense T) :
    IsClosed (f '' T) ∧ IsNowhereDense (f '' T) := by
  sorry

end AlgebraicGeometry
