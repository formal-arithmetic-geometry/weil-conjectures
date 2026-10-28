module

public import Sheaf.CategoryTheory.RouteInverseImageConstantSetComparison

/-! # Ring operations of the comparison on a single constant ring. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Ring-operation part of an inverse-image lift.

Source: Stacks Project, `sites.tex`, Tag 00YV
(blueprint: lem-route-inverse-image-constant-ring-operations). -/
structure RingInverseImage
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (R : Sheaf JC CommRingCat.{u})
    (RI : Sheaf JD CommRingCat.{u}) where
  ringUnderlying : L.obj ((sheafCompose JC (forget CommRingCat)).obj R) ≅
    (sheafCompose JD (forget CommRingCat)).obj RI
  ringAdd : ∀ (T : Sheaf JC (Type u))
    (a b t : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
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
  ringMul : ∀ (T : Sheaf JC (Type u))
    (a b t : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
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
  ringZero : ∀ (T : Sheaf JC (Type u))
    (a : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 0) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) = 0
  ringOne : ∀ (T : Sheaf JC (Type u))
    (a : T ⟶ ((sheafCompose JC (forget CommRingCat)).obj R)),
    (∀ (U : Cᵒᵖ) (x : T.obj.obj U), (@id (R.obj.obj U) (a.hom.app U x)) = 1) →
    ∀ (V : Dᵒᵖ) (x : (L.obj T).obj.obj V),
      (@id (RI.obj.obj V)
        (ringUnderlying.hom.hom.app V ((L.map a).hom.app V x))) = 1


/-- The underlying comparison with a single constant ring preserves its four operations.

Source: Stacks Project, Sites, Tag 00YV (rings as algebraic objects), and Tag 0H7J
(constant sheaves); original constant-comparison node, proof step 3.
(blueprint: lem-route-inverse-image-constant-ring-operations).

Proof: write the underlying sheaf of the constant ring as the constant set sheaf,
using `constantCommuteCompose`. The constant sheaf of `A × A` maps isomorphically
to the product of two copies of the constant sheaf of `A`, because set sheafification
preserves finite products. Its projections are the constant maps of the two
projections. Addition and multiplication composed with this isomorphism are the
constant maps of addition and multiplication: check this after precomposing with
the sheafification unit, where it is the ring-homomorphism property of that unit.
Naturality of `kappa` for the two projections and the two operations therefore
shows that the comparison transports addition and multiplication. Apply the
`ringAdd` and `ringMul` graph equations of `e` to this pair object. The pair
comparison and its image under `L` are isomorphisms (use finite-limit preservation),
so this checks every pair of target sections. For zero and one use the constant
singleton sheaf and the constant maps selecting zero and one. Naturality of
`kappa`, terminality, and `ringZero`/`ringOne` give the two nullary identities.
Finally conjugate these identities by `e.ringUnderlying`, which is invertible,
to obtain the displayed identities for its inverse followed by the comparison.
This argument works for the zero ring and for sites with empty covering sieves;
it never assumes injectivity of a sheafification unit or a final object of a site.
-/
theorem constantComparison_ring_operations
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasWeakSheafify JC CommRingCat.{u}] [HasWeakSheafify JD CommRingCat.{u}]
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (hL : PreservesFiniteLimits L)
    (kappa : constantSheaf JC (Type u) ⋙ L ≅ constantSheaf JD (Type u))
    (A : CommRingCat.{u}) (RI : Sheaf JD CommRingCat.{u})
    (e : RingInverseImage L ((constantSheaf JC CommRingCat.{u}).obj A) RI) :
    let f : ∀ U : Dᵒᵖ, RI.obj.obj U → ((constantSheaf JD CommRingCat.{u}).obj A).obj.obj U :=
      fun U x ↦ (e.ringUnderlying.inv ≫
        (constantRingSetComparison JC JD L kappa).hom.app A).hom.app U x
    ∀ U : Dᵒᵖ,
      f U 0 = 0 ∧ f U 1 = 1 ∧
      (∀ x y : RI.obj.obj U, f U (x + y) = f U x + f U y) ∧
      (∀ x y : RI.obj.obj U, f U (x * y) = f U x * f U y) := by
  sorry

end CategoryTheory
