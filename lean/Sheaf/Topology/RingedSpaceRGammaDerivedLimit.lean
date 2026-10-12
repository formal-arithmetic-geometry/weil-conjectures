/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Topology.OpenModuleDerivedSections
public import Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.Algebra.Homology.KInjectiveProducts
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.CategoryTheory.Triangulated.MilnorSequence
import Sheaf.CategoryTheory.Triangulated.RingedSpaceDerivedProducts
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit

/-!
# Cohomology over an open and derived inverse limits

Source: literature/stacks-project/cohomology.tex, Tag 0D60, label
lemma-RGamma-commutes-with-Rlim (blueprint: lem-pc-ringed-space-rgamma-derived-limit).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSpace

/-- Derived sections over an open preserve Roos triangles and satisfy the Milnor
short exact sequence.  The functor `RΓ(U,-)` is represented by K-injective
resolutions of complexes of modules, via `openModuleDerivedSections`.
Source: literature/stacks-project/cohomology.tex, Tag 0D60, label
lemma-RGamma-commutes-with-Rlim (blueprint: lem-pc-ringed-space-rgamma-derived-limit).

Proof, following Tag 0D60:
1. The site of opens is small. K-injective resolutions exist by
   `prop-pur-kinjective-resolutions-exist`, and sections preserve limits by
   `lem-weil-pbc-module-sheaves-limits-sectionwise`. The right derived functor
   is triangulated (`lem-pc-right-derived-functor-triangulated`). Products exist
   by `lem-pc-ringed-space-derived-products` and
   `lem-weil-derived-limit-existence`, using exact products in abelian groups
   (`lem-pc-abelian-groups-exact-products`).
2. Resolve each tower term by a K-injective complex. Its termwise product is
   K-injective and represents the derived product
   (`lem-pc-ringed-space-product-kinjective`). Sections identify it with the
   product of the sections complexes; exact products of abelian groups identify
   this with the target derived product (`lem-weil-derived-limit-existence`).
   The projection equations characterize the comparison. The triangulated
   functor sends the Roos triangle to the target Roos triangle
   (`lem-pc-homotopy-limit-map`, `def-weil-derived-limit`).
3. Apply the long exact cohomology sequence
   (`lem-sf-derived-homology-long-exact`). Exact products identify the cohomology
   of the product with the product of the cohomologies, with transition map
   `1 - s`. Its kernel is inverse limit and its cokernel is the first right
   derived inverse limit (`lem-pc-derived-limit-roos-abelian-groups`). The middle
   three terms give the short exact sequence (`lem-pc-derived-limit-milnor-sequence`).
   The right map is cohomology of `p` followed by each product projection, as
   specified by its equations with every limit projection.
-/
theorem rgamma_derivedLimit (X : RingedSpace.{u}) (U : TopologicalSpace.Opens X)
    [HasDerivedCategory.{v} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} AddCommGrpCat.{u}]
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (L : DerivedCategory (SheafOfModules.{u} (moduleRings X)))
    (p : L ⟶ ∏ᶜ (fun n : ℕ => K.obj (Opposite.op n)))
    (δ : (∏ᶜ (fun n : ℕ => K.obj (Opposite.op n))) ⟶ L⟦(1 : ℤ)⟧)
    (hK : IsDerivedLimitTriangle
      (fun n : ℕ => K.map (homOfLE (Nat.le_succ n)).op) L p δ) :
    (∃ e : (openModuleDerivedSections X U).obj (∏ᶜ (fun n : ℕ => K.obj (Opposite.op n))) ≅
        ∏ᶜ (fun n : ℕ => (openModuleDerivedSections X U).obj (K.obj (Opposite.op n))),
      (∀ n, e.hom ≫ Pi.π _ n = (openModuleDerivedSections X U).map (Pi.π _ n)) ∧
      IsDerivedLimitTriangle
        (fun n => (openModuleDerivedSections X U).map (K.map (homOfLE (Nat.le_succ n)).op))
        ((openModuleDerivedSections X U).obj L) ((openModuleDerivedSections X U).map p ≫ e.hom)
        (e.inv ≫ (openModuleDerivedSections X U).map δ ≫
          ((openModuleDerivedSections X U).commShiftIso (1 : ℤ)).hom.app L)) ∧
    (∀ m : ℤ, ∃ (a :
        (@Functor.rightDerived _ _ _ _ _
          (@InjectiveResolution.instHasInjectiveResolutions _ _ _
            roosTowerEnoughInjectives) _
          (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})
          roosLimitAdditive 1).obj
          (K ⋙ (openModuleDerivedSections X U) ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)) ⟶
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
          ((openModuleDerivedSections X U).obj L))
      (b : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
          ((openModuleDerivedSections X U).obj L) ⟶
        limit (K ⋙ (openModuleDerivedSections X U) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} m)),
      ∃ hz : a ≫ b = 0,
        (ShortComplex.mk a b hz).ShortExact ∧
        ∀ n, b ≫ limit.π
            (K ⋙ (openModuleDerivedSections X U) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} m)
            (Opposite.op n) =
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
            ((openModuleDerivedSections X U).map (p ≫ Pi.π _ n))) := by
  sorry

end AlgebraicGeometry.RingedSpace
