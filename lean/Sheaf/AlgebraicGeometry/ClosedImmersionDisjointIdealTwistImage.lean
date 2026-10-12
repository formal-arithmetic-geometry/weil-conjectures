module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Subobject.Limits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

/-! # Image of restriction on an ideal twist

Source: Stacks Project, Remark 09NW, the formula IB = (I+J)/J, and Lemma 09NX.
(blueprint: lem-sc-closed-immersion-disjoint-ideal-twist-image).
-/

/-- The ambient restriction of an ideal twist has the target ideal-product image.
No zero-intersection hypothesis is needed for this image calculation.

Source: Stacks Project, Remark 09NW, the formula IB = (I+J)/J, and the
local trivialization argument in Lemma 09NX.
(blueprint: lem-sc-closed-immersion-disjoint-ideal-twist-image).

Proof: put N = M.tensorPow m and use the canonical pullback adjunction first.
On an affine basis trivializing N, a closed immersion is a quotient A -> B = A/J.
Write K for the ideal of I. The source multiplication image has sections K, and
the unit sends a in K to its residue class in B. Its image is (K+J)/J = KB:
every element of this quotient ideal is the residue class of an element of K.
The adjoint ideal map B tensor_A K -> B sends b tensor a to b times the residue
of a and therefore has the same ideal KB as image. Multiplying this ideal by
N restricted to X gives exactly the image of the ambient restriction.
An arbitrary linear comparison e preserves this statement: a B-linear
isomorphism sends (KB) times its source onto (KB) times its target, with inverse
e.inv. Changing the adjunction precomposes the adjoint ideal map by an
isomorphism, so does not change its image; the component on N similarly
transports the ambient map by a linear isomorphism, preserving the ideal product.
Image sheaves are locally the multiplication images just calculated: all these
modules are quasi-coherent on the affine basis, and a closed immersion is affine.
Equality of these subsheaves on the basis gives equality globally, since local
membership glues. This computes sheaf images, not images of sections on arbitrary
opens. Empty inverse images give zero modules, as do K = 0; J = 0 and m = 0 are
included. There is no assertion that K -> KB is injective. -/
theorem closedImmersion_disjointIdeal_twist_image {Y X : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] (I : Y.IdealSheafData)
    (M : Y.Modules) [M.IsInvertible] (m : ℕ)
    (e : (tensorPullback i).obj (M.tensorPow m) ≅
      ((tensorPullback i).obj M).tensorPow m) :
    let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
    let φ := (adj.homEquiv I.toModules (SheafOfModules.unit X.ringCatSheaf)).symm
      (I.toModulesι ≫ SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)
    let μ := I.toModulesι ▷ M.tensorPow m ≫ (λ_ (M.tensorPow m)).hom
    let μ₁ := image.ι φ ▷ ((tensorPullback i).obj M).tensorPow m ≫
      (λ_ (((tensorPullback i).obj M).tensorPow m)).hom
    imageSubobject (image.ι μ ≫ adj.unit.app (M.tensorPow m) ≫
      (pushforward i).map e.hom) = imageSubobject ((pushforward i).map (image.ι μ₁)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
