/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Sheaf.AlgebraicGeometry.RelativeModuliInertia
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Homeomorph.Defs
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.StackPointTopology
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Separated targets of universal homeomorphisms from algebraic stacks

Source: Stacks Project, stacks-more-morphisms.tex, Tag 0DUY, separatedness argument;
spaces-morphisms.tex, Tag 04Y0 (blueprint:
lem-sfb-stack-universal-homeomorphism-separated-target).

Both topological hypotheses are tested on actual algebraic-stack 2-base changes.
The conclusion tests the algebraic-space diagonal by scheme closed immersions.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A universal homeomorphism from a stack with universally closed relative diagonal
has a separated algebraic-space target, with no finiteness assumption on the map.
Source: Stacks Project, Tags 0DUY and 04Y0
(blueprint: lem-sfb-stack-universal-homeomorphism-separated-target).

Proof:
1. Factor f × f through Q × Z. Both factors are base changes of f, hence induce
homeomorphisms after every further base change. Their composite does too. Use
lem-sfb-algebraic-stack-fibre-products and lem-sfb-stack-point-topology.
2. For an algebraic space T over Q × Q put D = Q ×_(Q×Q) T,
B = (Z × Z) ×_(Q×Q) T and A = Z ×_(Q×Q) T. The square A → B over D → T
has vertical maps which are base changes of f and f × f. Its top map is a base
change of the source diagonal. The vertical point maps are homeomorphisms and
the top point map is closed. The products and their reassociations use
lem-sfb-algebraic-stack-fibre-products and lem-trf-space-fibre-products-etale-covers.
3. For closed C in |D|, its inverse image in |A| is closed. Its image in |B|
is closed, and then its image in |T| is closed. Commutativity and surjectivity
of |A| → |D| identify this image with the image of C under |D| → |T|.
The topology comparison of lem-sfb-stack-point-topology identifies these with
ordinary algebraic-space point topologies. Thus the target diagonal is universally closed.
4. Apply lem-sfb-space-separated-diagonal-closed over Spec k to Q → Spec k.
Tag 04Y0 makes its diagonal a representable closed immersion, exactly the
scheme-test conclusion below. No finite type, adequacy or inertia hypothesis is used. -/
theorem stack_universalHomeomorphism_separated_target {k : Type u} [Field k]
    (Z : BasedCategory.{v₁, w₁} (Over (Spec (.of k))))
    (Q : AlgebraicSpace (Spec (.of k))) (hZ : IsAlgebraicModuliStack Z)
    (f : BasedFunctor Z (discreteModuli Q.obj.obj))
    (hf : ∀ (T : BasedCategory.{max u v₁ v₂, max (u + 1) w₁ w₂}
        (Over (Spec (.of k)))), IsAlgebraicModuliStack T →
      ∀ t : BasedFunctor T (discreteModuli Q.obj.obj),
        IsHomeomorph (moduliPointMap (moduliTwoFiberFst t f)))
    (hdiag : ∀ (T : BasedCategory.{max u v₁ v₂, max (u + 1) w₁ w₂}
        (Over (Spec (.of k)))), IsAlgebraicModuliStack T →
      ∀ t : BasedFunctor T
          (moduliTwoFiberProduct (moduliBaseStructure Z) (moduliBaseStructure Z)),
        IsClosedMap (moduliPointMap
          (moduliTwoFiberFst t (moduliRelativeDiagonal (moduliBaseStructure Z))))) :
    AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (prod.lift (𝟙 Q.obj.obj) (𝟙 Q.obj.obj)) := by
  sorry

end CategoryTheory
