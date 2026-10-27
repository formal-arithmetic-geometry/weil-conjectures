/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.AdequateModuliSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets
import Sheaf.AlgebraicGeometry.AdequateModuliTopologicalImages

/-! # Universal submersiveness of adequate moduli spaces

Source: Alper, arXiv:1005.2398v3, Theorem 5.3.1(1)--(3), and Stacks Project,
Tags 04XH and 04XL (blueprint: lem-sfb-adequate-moduli-universally-submersive).

Algebraic spaces are used as their discrete fibred groupoids. Their point sets and
smooth-atlas topologies are the existing stack constructions; an etale atlas is smooth
and gives the usual algebraic-space topology. The base change is the actual 2-fibre product.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry

namespace CategoryTheory

/-- Every algebraic-space base change of an adequate moduli space is a surjection
and detects open subsets on the target. No finiteness or separatedness of the target
or flatness of the base change is assumed.
Source: Alper, arXiv:1005.2398v3, Theorem 5.3.1(1)--(3); Stacks, Tags 04XH and 04XL
(blueprint: lem-sfb-adequate-moduli-universally-submersive).

Proof:
1. Fix T -> Y. The node lem-sfb-adequate-moduli-topological-images gives surjectivity
of |F| -> |Y|. The image/base-change assertion of
lem-sfb-smooth-presentation-closed-subsets identifies the image of the second projection
with the inverse image of that full image, so the second projection is surjective.
The same topology node supplies continuity and identifies the atlas topologies.
2. Apply lem-sfb-adequate-moduli-topological-images to the original adequate morphism:
the second projection is closed for every algebraic-space T -> Y. Its own adequacy is
not asserted, and no flatness of T -> Y is used.
3. Continuity pulls open subsets back to open subsets. Conversely, if the inverse image
of V is open, the inverse image of its complement is closed. Closedness of the projection
makes its image closed, and surjectivity identifies that image with the complement of V.
Thus V is open. This applies to every T -> Y, including the empty space. -/
theorem adequate_moduli_universally_submersive (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hF : IsAlgebraicModuliStack F)
    (Y : AlgebraicSpace (Spec (.of k)))
    (φ : BasedFunctor F (discreteModuli Y.obj.obj))
    (hφ : IsAdequateModuliSpace F hF Y φ) :
    ∀ (T : AlgebraicSpace (Spec (.of k))) (g : T ⟶ Y),
      Function.Surjective (moduliPointMap (moduliTwoFiberSnd φ
        (discreteModuliMap g.hom.hom))) ∧
      ∀ V : Set (ModuliPoints (discreteModuli T.obj.obj)),
        @IsOpen _ (moduliPointTopologicalSpace (discreteModuli T.obj.obj)) V ↔
          @IsOpen _ (moduliPointTopologicalSpace
            (moduliTwoFiberProduct φ (discreteModuliMap g.hom.hom)))
            (moduliPointMap (moduliTwoFiberSnd φ (discreteModuliMap g.hom.hom)) ⁻¹' V) := by
  sorry

end CategoryTheory
