/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.SmoothPresentationClosedSubsets
public import Sheaf.AlgebraicGeometry.ModuliSchemeBaseChange
public import Sheaf.AlgebraicGeometry.AdequateGeometricFibresSubmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Images of geometric points with intersecting closures

Source: Alper, arXiv:1005.2398v3, Proposition 7.1.1, proof, printed p.36;
Stacks Project, Tags 088J, 08AL, 07U5, 04XL and 04XH
(blueprint: lem-sfb-locally-separated-closure-equivalent-images).

Closures are taken in the smooth-atlas topology after extension to the given field.
An isomorphism in the discrete target fibre expresses equality of its rational points.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A map to a locally separated algebraic space identifies geometric objects whose
singleton closures meet after scalar extension.
Source: Alper, arXiv:1005.2398v3, Proposition 7.1.1, proof, printed p.36;
Stacks Project, Tags 088J, 08AL, 07U5, 04XL and 04XH
(blueprint: lem-sfb-locally-separated-closure-equivalent-images).

Proof:
1. Write H = h_Ω and let a₁,a₂ : Spec Ω → Z_Ω be the two images. By
lem-sfb-locally-separated-rational-point-closed-immersion each aᵢ is a closed
immersion, and its singleton image is closed. No finite type or quasi-separatedness
hypothesis is needed.
2. Choose a point in the intersection of the two singleton closures. The continuity
clause of lem-sfb-smooth-presentation-closed-subsets, applied over Ω to H, says the
inverse image of each closed image singleton is closed. It contains the corresponding
source point and therefore its closure. The common point maps to both image points,
so their underlying points agree.
3. Form P = Spec Ω ×_{Z_Ω} Spec Ω from a₁,a₂, using def-pc-fibre-product. The
point-surjectivity clause of lem-sfb-smooth-presentation-closed-subsets makes P nonempty.
The scheme-test clause of the rational-point closed-immersion lemma makes P a scheme
closed in Spec Ω. By def-weil-closed-immersion and def-weil-affine-spectrum it is
Spec (Ω/I); nonemptiness makes I proper, so I = 0 by def-weil-field. Its projection
is an isomorphism. Composing its inverse with either projection gives the identity
Ω-morphism of Spec Ω. The pullback equality now gives a₁ = a₂, equivalently an
isomorphism between the images in the discrete fibre. -/
theorem locallySeparated_closureEquivalent_images (k : Type u) [Field k]
    (F : BasedCategory.{v, w} (Over (Spec (.of k))))
    (hF : IsAlgebraicModuliStack F) (Z : AlgebraicSpace (Spec (.of k)))
    (hZ : AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left)
      (prod.lift (𝟙 Z.obj.obj) (𝟙 Z.obj.obj)))
    (h : BasedFunctor F (discreteModuli Z.obj.obj))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Spec (.of k))
    (x₁ x₂ : Functor.Fiber F.p (Over.mk g))
    (hx : ((@closure _ (moduliSmoothPointTopology (moduliSchemeBaseChange F g))
        {moduliScalarPoint F Ω g x₁}) ∩
      (@closure _ (moduliSmoothPointTopology (moduliSchemeBaseChange F g))
        {moduliScalarPoint F Ω g x₂})).Nonempty) :
    Nonempty ((moduliFiberMap h (Over.mk g)).obj x₁ ≅
      (moduliFiberMap h (Over.mk g)).obj x₂) := by
  sorry

end CategoryTheory
