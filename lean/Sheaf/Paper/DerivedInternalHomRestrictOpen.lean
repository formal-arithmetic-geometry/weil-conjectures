/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.Paper.DerivedHomMayerVietoris
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# Derived internal Hom commutes with restriction to opens

Source: literature/stacks-project/cohomology.tex, Lemma 08DL
(blueprint: lem-sc-derived-internal-hom-restrict-open).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
universe u w


namespace CategoryTheory

/-- Restriction of derived internal Hom to an open agrees canonically with the
internal Hom of the restricted objects.

Source: literature/stacks-project/cohomology.tex, Lemma 08DL.
Proof:
1. Represent the second argument by a functorial K-injective resolution
   (`prop-pur-kinjective-resolutions-exist`); compute Hom using
   `def-pur-derived-internal-hom`.
2. By `lem-sc-derived-k-injective-restrict-open`, restriction preserves K-injectives.
   It is exact, so the restricted
   resolution computes the restricted derived internal Hom.
3. By `def-pur-sheaf-hom` and `def-pur-hom-complex`, the sheaf Hom complexes
   agree termwise after restriction, including products
   and differentials, giving an isomorphism in the derived category.
4. Pass the complex isomorphism to the derived category. Its components restrict
   local maps, so it is natural in both arguments and successive open inclusions.
   Representative and resolution independence follows from
   `def-pur-derived-internal-hom`.
(Uses `def-pur-derived-internal-hom` and the open restriction K-injective lemma.)
(blueprint: lem-sc-derived-internal-hom-restrict-open). -/
theorem derivedInternalHom_restrict_open
    (X : RingedSpace.{u}) (U : Opens X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [hU : HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over U))]
    (K L : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    Nonempty (
      (@derivedInternalHom.{u, w} (Over U) _
          ((Opens.grothendieckTopology X).over U) (X.sheaf.over U) hU).obj
        (op ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj K),
          ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj L)) ≅
      ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj
        ((derivedInternalHom.{u, w} (Opens.grothendieckTopology X) X.sheaf).obj
          (op K, L)))) := by
  sorry

end CategoryTheory
