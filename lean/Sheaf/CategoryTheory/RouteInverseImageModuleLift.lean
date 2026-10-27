module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Module lift for a transported ring sheaf

Source: Stacks Project, `sites-modules.tex`, Tags 03D2 and 03D7
(blueprint: lem-route-inverse-image-module-lift).

The statement records the sectionwise transport of module operations through a
finite-limit-preserving inverse-image functor.  Its conclusion is the existing
`AlgebraicInverseImage` presentation, with the supplied ring comparison fixed
literally as its `ringUnderlying` field.
-/

@[expose] public section

set_option autoImplicit false

universe u vC vD

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- A finite-limit-preserving inverse image transports a specified ring sheaf
comparison to a module inverse-image presentation.

Source: Stacks Project, `sites-modules.tex`, Tag 03D2.
(blueprint: lem-route-inverse-image-module-lift)
The proof transports addition, zero,
multiplication, one, module addition, zero, and scalar multiplication along
the finite-product comparisons supplied by `PreservesFiniteLimits`; the
sectionwise module axioms and restriction compatibilities then give the
functor and its underlying natural isomorphism.  The generalized-section
graph equations are exactly the fields of `AlgebraicInverseImage`, and the
ring comparison is retained as the given `e_R`.
-/
theorem exists_module_lift
    {C : Type u} {D : Type u} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf K CommRingCat.{u})
    (e_R : L.obj ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ≅
      (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)
    (h_add : ∀ (T : Sheaf J (Type u))
      (a b t : T ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)),
      (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
        (@id (R.obj.obj U) (t.hom.app U x)) =
          (@id (R.obj.obj U) (a.hom.app U x)) +
            (@id (R.obj.obj U) (b.hom.app U x))) →
      ∀ (W : Dᵒᵖ) (x : (L.obj T).obj.obj W),
        (@id (A.obj.obj W) (e_R.hom.hom.app W ((L.map t).hom.app W x))) =
          (@id (A.obj.obj W) (e_R.hom.hom.app W ((L.map a).hom.app W x))) +
            (@id (A.obj.obj W) (e_R.hom.hom.app W ((L.map b).hom.app W x))))
    (h_mul : ∀ (T : Sheaf J (Type u))
      (a b t : T ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)),
      (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
        (@id (R.obj.obj U) (t.hom.app U x)) =
          (@id (R.obj.obj U) (a.hom.app U x)) *
            (@id (R.obj.obj U) (b.hom.app U x))) →
      ∀ (W : Dᵒᵖ) (x : (L.obj T).obj.obj W),
        (@id (A.obj.obj W) (e_R.hom.hom.app W ((L.map t).hom.app W x))) =
          (@id (A.obj.obj W) (e_R.hom.hom.app W ((L.map a).hom.app W x))) *
            (@id (A.obj.obj W) (e_R.hom.hom.app W ((L.map b).hom.app W x))))
    (h_zero : ∀ (T : Sheaf J (Type u))
      (a : T ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)),
      (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
        (@id (R.obj.obj U) (a.hom.app U x)) = 0) →
      ∀ (W : Dᵒᵖ) (x : (L.obj T).obj.obj W),
        (@id (A.obj.obj W) (e_R.hom.hom.app W ((L.map a).hom.app W x))) = 0)
    (h_one : ∀ (T : Sheaf J (Type u))
      (a : T ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)),
      (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
        (@id (R.obj.obj U) (a.hom.app U x)) = 1) →
      ∀ (W : Dᵒᵖ) (x : (L.obj T).obj.obj W),
        (@id (A.obj.obj W) (e_R.hom.hom.app W ((L.map a).hom.app W x))) = 1) :
    ∃ I : AlgebraicInverseImage L R A, I.ringUnderlying = e_R := by
  sorry

end SheafOfModules

