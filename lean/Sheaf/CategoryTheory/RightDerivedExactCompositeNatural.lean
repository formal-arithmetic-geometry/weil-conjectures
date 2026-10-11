/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.CategoryTheory.RightDerivedExactComposite

/-!
# Naturality of the exact-composite comparison

Source: Stacks Project, Tag 015E, applied to the resolutions in Tag 015M
(blueprint: lem-sc-ext-derived-composite-natural).
-/

universe u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- (blueprint: lem-sc-ext-derived-composite-natural) The canonical exact-composite
comparisons commute with a natural transformation between the exact functors.
The comparisons are the witnesses of `exists_rightDerived_exact_comp_iso`: their homs
are characterized there as the acyclic-resolution comparisons for every resolution and lift.
The map on the upper side is explicitly cohomology of `U(α)` on the resolution `I`,
transported to the right-derived objects by `I.isoRightDerivedObj`.

Source: Stacks Project, Tag 015E, naturality of the canonical acyclic comparison,
applied to the resolutions of Tag 015M.

Proof: choose the injective resolution `I` of `M` (def-sp-injective-resolutions).
Exactness of `T` and `T'` makes their images resolutions of `T(M)` and `T'(M)`.
Their terms are `U`-acyclic by `hTU` and `hT'U` (def-sp-acyclic).
Naturality of `α` on the augmentation makes its complex map a map over `α.app M`.
Apply lem-sc-acyclic-comparison-natural with these two resolutions, the object map
`α.app M`, and the complex map given by the components of `α`. The comparisons are
those of lemma-weil-pbc-leray-acyclicity, item 2, and hence the comparisons characterized
by lem-sc-ext-derived-composite. Transport the resulting cohomology square along
`I.isoRightDerivedObj` for both composites. Its top map is precisely the displayed
cohomology map (equivalently `NatTrans.rightDerived (whiskerRight α U) i` by
`InjectiveResolution.rightDerived_app_eq`), giving the asserted equality. -/
theorem rightDerived_exact_comp_iso_naturality
    {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
    [Abelian A] [Abelian B] [Abelian C] [EnoughInjectives A] [EnoughInjectives B]
    (T T' : A ⥤ B) (U : B ⥤ C)
    [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [T'.Additive] [PreservesFiniteLimits T'] [PreservesFiniteColimits T']
    [U.Additive] [PreservesFiniteLimits U]
    (hTU : ∀ (J : A), Injective J → U.rightAcyclic (T.obj J))
    (hT'U : ∀ (J : A), Injective J → U.rightAcyclic (T'.obj J))
    (α : T ⟶ T') (M : A) (I : InjectiveResolution M) (i : ℕ) :
    let cT := Classical.choose (exists_rightDerived_exact_comp_iso T U hTU M i)
    let cT' := Classical.choose (exists_rightDerived_exact_comp_iso T' U hT'U M i)
    (I.isoRightDerivedObj (T ⋙ U) i).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (whiskerRight α U) (ComplexShape.up ℕ)).app
            I.cocomplex) i ≫
        (I.isoRightDerivedObj (T' ⋙ U) i).inv ≫ cT'.hom =
      cT.hom ≫ (U.rightDerived i).map (α.app M) := by
  sorry

end CategoryTheory.Functor
