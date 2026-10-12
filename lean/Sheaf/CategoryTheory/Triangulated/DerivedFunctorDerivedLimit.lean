/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Algebra.Homology.KInjectiveProducts
import Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit

/-!
# Right derived functors and countable derived limits

Source: Stacks Project, Injectives, Lemma Tag 08U1
(blueprint: lem-pc-derived-functor-commutes-derived-limit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- If an additive functor on sheaves of modules commutes with countable products,
its unbounded right derived functor sends every specified Roos triangle to a Roos
triangle. The comparison of product vertices respects each projection.

Choose the Roos triangle for `L`. Represent the terms of the tower by K-injective
complexes. Their termwise product is K-injective and computes the product in the
derived category (blueprint: lem-pc-ringed-space-product-kinjective). Product
preservation by `F` identifies its image with the product of the images; the
derived-product construction gives the target product
(blueprint: lem-weil-derived-limit-existence). The right derived functor is
triangulated (blueprint: lem-pc-right-derived-functor-triangulated). Its image
of the source Roos triangle is therefore distinguished, and the product
comparison identifies its middle map with the target transition endomorphism
(blueprint: lem-pc-homotopy-limit-map). This gives a Roos triangle for the image,
so the image is a derived limit (blueprint: def-weil-derived-limit).
Stacks Project, Injectives, Lemma Tag 08U1
(blueprint: lem-pc-derived-functor-commutes-derived-limit). -/
theorem rightDerivedFunctor_isDerivedLimitTriangle (X : Scheme.{u})
    (F : X.Modules ⥤ AddCommGrpCat.{u}) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    [Abelian.HasKInjectiveResolutions X.Modules]
    [Abelian.HasKInjectiveResolutions AddCommGrpCat.{u}]
    [HasDerivedCategory X.Modules] [HasDerivedCategory AddCommGrpCat.{u}]
    {K : ℕ → DerivedCategory X.Modules}
    (f : ∀ n, K (n + 1) ⟶ K n) (L : DerivedCategory X.Modules)
    (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (h : CategoryTheory.IsDerivedLimitTriangle f L p δ) :
    ∃ e : F.rightDerivedFunctor.obj (∏ᶜ K) ≅
        ∏ᶜ (fun n => F.rightDerivedFunctor.obj (K n)),
      (∀ n, e.hom ≫ Pi.π _ n = F.rightDerivedFunctor.map (Pi.π K n)) ∧
      CategoryTheory.IsDerivedLimitTriangle (fun n => F.rightDerivedFunctor.map (f n))
        (F.rightDerivedFunctor.obj L) (F.rightDerivedFunctor.map p ≫ e.hom)
        (e.inv ≫ F.rightDerivedFunctor.map δ ≫
          (F.rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app L) := by
  sorry

end AlgebraicGeometry.Scheme
