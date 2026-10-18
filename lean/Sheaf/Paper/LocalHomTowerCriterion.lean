/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.CategoryTheory.LocalCoefficientLocalization
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.CategoryTheory.SliceAwayLocalizationFreeResolution
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-!
# Localization internal Hom and the multiplication tower

Source: Stacks Project, algebraization.tex, Tag 0997, lemma-hom-from-Af,
equivalence of (1) and (3) (blueprint: lem-weil-pbc-local-hom-tower-criterion).
-/

@[expose] public section

universe u w wSlice

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Internal RHom from the coefficient localization vanishes exactly when a derived limit
of the multiplication tower vanishes, on the slice site.

Source: Stacks Project, algebraization.tex, Tag 0997, lemma-hom-from-Af,
equivalence of (1) and (3) (blueprint: lem-weil-pbc-local-hom-tower-criterion).

Proof:
1. Work on the small slice site and choose a degreewise injective K-injective replacement
   of the restricted complex (prop-pur-kinjective-resolutions-exist). The derived internal
   Hom definition computes RHom into this replacement.
2. The free resolution of the localization (lem-weil-pbc-localization-free-resolution)
   gives a distinguished triangle (lem-weil-pbc-complex-ses-triangle). Apply contravariant
   derived internal Hom and rotate (lem-weil-pbc-ringed-internal-hom-exact-restriction).
3. Hom from the countable free sum is the product of copies of the replacement, and
   precomposition with the resolution map sends (x_n) to (x_n - f*x_(n+1))
   (def-pur-sheaf-hom and def-pur-hom-complex).
4. Products of K-injectives represent derived products
   (lem-pc-ringed-space-product-kinjective), so the triangle obtained is the Roos triangle
   of the multiplication tower (def-weil-derived-limit). Reindex n ≥ 0 as n+1 ≥ 1.
5. Any chosen derived limit is isomorphic to this one (lem-weil-derived-limit-existence).
   Isomorphic objects vanish simultaneously. No exactness of products of sheaves is assumed. -/
theorem localHom_zero_iff_multiplicationTower_zero
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (U : C) (f : R.obj.obj (op U))
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (localCoefficientRings R))]
    [HasDerivedCategory.{wSlice} (ringedSiteModules.{u} ((localCoefficientRings R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u} (localCoefficientRings R)))
    [HasProduct (fun _ : ℕ ↦ (localCoefficientDerivedRestriction R U).obj K)]
    (T : DerivedCategory (ringedSiteModules.{u} ((localCoefficientRings R).over U)))
    (_hT : IsDerivedLimit
      (K := fun _ : ℕ ↦ (localCoefficientDerivedRestriction R U).obj K)
      (fun _ ↦ (localSectionDerivedMultiplication R U f).app K) T) :
    IsZero ((derivedInternalHom (J.over U) (R.over U)).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj (localCoefficientLocalization R U f)),
        (localCoefficientDerivedRestriction R U).obj K)) ↔ IsZero T := by
  sorry

end CategoryTheory
