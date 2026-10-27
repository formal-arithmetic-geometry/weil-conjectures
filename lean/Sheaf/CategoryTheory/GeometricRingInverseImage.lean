/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # Ring transport along a geometric inverse image

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tag 03D2.
(blueprint: lem-weil-pbc-coherent-ring-inverse-image).
-/

@[expose] public section
set_option autoImplicit false
universe u w uC vC uD vD
open CategoryTheory
namespace SheafOfModules
/-- The ring-only part of algebraic inverse image, specified on arbitrary generalized
sections. It includes no module functor or module operation.
Source: Stacks Project, Sites, Tag 00YV (rings as algebraic objects).
(blueprint: def-weil-pbc-ring-inverse-image). -/
structure RingInverseImage
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (L : Sheaf JC (Type (w)) ⥤ Sheaf JD (Type (w)))
    (R : Sheaf JC CommRingCat.{w})
    (RI : Sheaf JD CommRingCat.{w}) where
  ringUnderlying : L.obj ((sheafCompose JC
      (CategoryTheory.forget CommRingCat.{w})).obj R) ≅
    (sheafCompose JD (CategoryTheory.forget CommRingCat.{w})).obj RI
  ringAdd : ∀ (T : Sheaf JC (Type (w)))
    (a b t : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) + (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map t).hom.app V x))) =
        (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) +
          (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map b).hom.app V x)))
  ringMul : ∀ (T : Sheaf JC (Type (w)))
    (a b t : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
      (@id (R.obj.obj U) (t.hom.app U x)) =
        (@id (R.obj.obj U) (a.hom.app U x)) * (@id (R.obj.obj U) (b.hom.app U x))) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map t).hom.app V x))) =
        (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) *
          (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map b).hom.app V x)))
  ringZero : ∀ (T : Sheaf JC (Type (w)))
    (a : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 0) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) = 0
  ringOne : ∀ (T : Sheaf JC (Type (w)))
    (a : T ⟶ ((sheafCompose JC (CategoryTheory.forget CommRingCat.{w})).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 1) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) = 1

end SheafOfModules

namespace CategoryTheory.ConstantCompletion

open CategoryTheory.Limits

/-- Coherent inverse image of ring sheaves, including the natural constant comparison.
Source: Stacks Project, Sites, Tag 00YV (ring objects and constant objects), and
Modules on Sites, Tag 03D2.
(blueprint: lem-weil-pbc-coherent-ring-inverse-image).

Proof: identify a ring sheaf with a commutative ring object in the category of set
sheaves. Apply L to its underlying object and every operation, using the inverse
finite-product comparisons for binary operations and the inverse terminal comparison
for zero and one. The ring identities follow by applying L to their finite-product
identity diagrams. On a ring morphism use L of its underlying morphism; the operation
comparison equations show this is a ring morphism. The underlying maps then satisfy
the displayed naturality equation. Since L is a left adjoint preserving the terminal
object, it preserves coproducts of terminal objects. A constant set sheaf is such a
coproduct. The resulting natural constant-set isomorphism preserves every operation:
check on the summands indexed by the operands and use the product comparison.
It therefore lifts to the natural isomorphism of constant ring sheaves. The graph
identities follow by expressing each generalized operation as the universal operation
precomposed with the tuple of its operands. -/
theorem coherentRingInverseImage_exists
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] :
    ∃ (F : Sheaf J CommRingCat.{u} ⥤ Sheaf K CommRingCat.{u})
      (d : ∀ R : Sheaf J CommRingCat.{u}, SheafOfModules.RingInverseImage L R (F.obj R)),
      (∀ {R S : Sheaf J CommRingCat.{u}} (f : R ⟶ S),
        L.map ((sheafCompose J (forget CommRingCat)).map f) ≫ (d S).ringUnderlying.hom =
          (d R).ringUnderlying.hom ≫ (sheafCompose K (forget CommRingCat)).map (F.map f)) ∧
      Nonempty (constantSheaf J CommRingCat.{u} ⋙ F ≅ constantSheaf K CommRingCat.{u}) := by
  sorry

end CategoryTheory.ConstantCompletion
