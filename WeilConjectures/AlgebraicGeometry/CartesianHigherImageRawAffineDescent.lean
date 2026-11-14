/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
import WeilConjectures.AlgebraicGeometry.CartesianHigherImageAffineComplexPresentation
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawComplexPresentation
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Affine derived classes for cartesian higher images

## References

* Stacks Project, Tag 0EYM
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

noncomputable local instance cartesianHigherImageRawAffineDescentHasShift (T : Scheme.{u}) :
    HasShift (DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) ℤ :=
  inferInstance

/-- A raw derived class on an affine etale test object factors through a pulled-back
stage derived image (Stacks, Tags 0EYM, 0EYL, 09YQ). -/
theorem exists_cartesianHigherImage_raw_affine_factorization
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) [IsAffine U.left]
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj U) ⟶
        (cartesianDerivedImage f c.pt.hom
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦(q : ℤ)⟧) :
    ∃ (i : I)
      (t : (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((abelianComparisonFree c.pt.left).obj U) ⟶
          ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
            (cartesianDerivedImage f (D.obj i).hom
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧),
      t ≫ (shiftFunctor _ (q : ℤ)).map
        (cartesianDerivedImageMap f (D.obj i).hom c.pt.hom (c.π.app i).left
          (Over.w (c.π.app i)).symm ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) = z := by
  classical
  obtain ⟨J, _, _, H, B, a, lift, e, hB, hcompat⟩ :=
    exists_cartesianHigherImage_affine_complex_presentation D c hc f F q U
  obtain ⟨hcolim⟩ := EtaleComplexCohomologyPresentation.isColimit hB
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (forget AddCommGrpCat.{u + 1})
  obtain ⟨j, x, hx⟩ := Concrete.isColimit_exists_rep H hcolim (e.inv z)
  refine ⟨a j.unop, lift j.unop x, ?_⟩
  rw [hcompat, hx]
  exact ConcreteCategory.congr_hom e.inv_hom_id z

end AlgebraicGeometry.Etale
