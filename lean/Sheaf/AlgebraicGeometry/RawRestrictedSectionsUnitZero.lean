/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RawRestrictedHomotopySectionsIso
import Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison
import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap

/-! # Degree-zero normalization of the restricted sections unit

Source: Stacks Project, Cohomology on Sites, Tags 072W and 0BKV.
(blueprint: lem-sbc-raw-restricted-sections-unit-zero).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- The derived-sections unit transported through the localization comparisons.
Source: Stacks Project, Tags 072W and 0BKV.
(blueprint: lem-sbc-raw-restricted-sections-unit-zero). -/
noncomputable def sectionsUnit {Y : Scheme.{v}} (W : Y.Etale)
    (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :
    DerivedCategory.Q.obj (((underivedSections W).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.obj
        ((upperStar AddCommGrpCat.{v + 1} W.hom).mapDerivedCategory.obj
          (DerivedCategory.Q.obj K)) :=
  let L := upperStar AddCommGrpCat.{v + 1} W.hom
  let R := Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}
  let LK := (L.mapHomologicalComplex (.up ℤ)).obj K
  (DerivedCategory.quotientCompQhIso _).inv.app
      ((R.mapHomologicalComplex (.up ℤ)).obj LK) ≫
    R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj LK) ≫
    R.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app LK) ≫
    R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.inv.app K)

/-- On a single sheaf the homology of the transported unit is the inverse of
`zeroIso`, after identifying single-complex homology with underived sections.
Source: Stacks Project, Tags 072W and 0BKV (degree-zero derived sections).
(blueprint: lem-sbc-raw-restricted-sections-unit-zero).

Proof: expand `zeroIso` into the exact-restriction single comparison, the
unbounded-to-bounded-below derived comparison, the injective-resolution homology
comparison, and the classical degree-zero comparison. The compatibility of the
two derived functors with their units, given by `Functor.rightDerivedNatTrans_app`,
cancels the unbounded-to-bounded-below comparison. Apply the proved
`Functor.rightDerivedPlusSingleUnitHomology_comp_comparison` to the restricted
sheaf: it identifies the bounded-below single unit with `toRightDerivedZero`.
Since sections preserve finite limits, `rightDerivedZeroIsoSelf` is its inverse.
Thus the classical comparison cancels the same augmentation. The single-complex
homology isomorphism identifies its source with the sheaf of sections. Naturality
of exact restriction's single-complex comparison and homology's localization
comparison gives the
displayed equality. This argument requires no K-injectivity of the single
sheaf, and includes the zero sheaf and the empty etale object. -/
theorem sectionsUnit_zero {Y : Scheme.{v}} (W : Y.Etale)
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (underivedSingleIso W A).inv ≫
        ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} 0).app
          (((underivedSections W).mapHomologicalComplex (.up ℤ)).obj
            ((CochainComplex.singleFunctor _ 0).obj A))).inv ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
          (sectionsUnit W ((CochainComplex.singleFunctor _ 0).obj A)) =
      (zeroIso W A).inv := by sorry

end AlgebraicGeometry.Etale.RawRestrictedComparison
