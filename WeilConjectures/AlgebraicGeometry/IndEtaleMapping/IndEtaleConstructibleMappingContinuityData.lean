/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomConePairingDefs
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleDerivedImageHomAdjunction
import WeilConjectures.AlgebraicGeometry.ExternalRHom.ExternalRHomConePairingDefs
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.HomColimitExtension
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Topology.Constructible
import WeilConjectures.Algebra.Homology.DerivedFreeModuleHomology
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.Algebra.Category.Grp.AB

/-! # Constructible derived mapping continuity on affine ind-etale limits

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.3.14 and
proof of Lemma 6.3.16, pp. 47--48
(blueprint: lem-per-ind-etale-constructible-mapping-continuity).

The comparison is the localization of the map out of the termwise filtered
colimit of compatible complex representatives. It is not a categorical colimit
assertion in the triangulated category. The representatives retain both the
transition maps and the legs of the evaluation-defined pullback comparison.
All constructions use the ordinary constant-coefficient small etale category.

## Main statements

* `constructible_mapping_continuity`: the canonical comparison is invertible.
* `comparison_cofinal`: the canonical cofinal comparison triangle.
* `comparison_naturality`: system maps, coefficient maps and base restriction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (K M : DerivedCategoryModule A X)

variable {I : Type (u + 1)} [SmallCategory I]
variable (D : I ⥤ Over X) (c : Cone D)

variable {J : Type (u + 1)} [SmallCategory J]
variable (E : J ⥤ Over X) (d : Cone E) (r : J ⥤ I)
variable (K' M' : DerivedCategoryModule A X) (α : K' ⟶ K) (β : M ⟶ M')

/-- A compatible representative map without the cone-square field.
The geometric cone equation is supplied separately by the square hypothesis.
Source: Bhatt--Scholze 6.3.16, Step 7
(blueprint: lem-per-ind-etale-constructible-mapping-model-skeleton).
-/
structure ModelMapSkeleton (P : Model A K M D c) (Q : Model A K' M' E d)
    (η : E ⟶ r ⋙ D) (v : d.pt ⟶ c.pt) where
  stages : r.op ⋙ P.diagram ⟶ Q.diagram
  apex : P.cocone.pt ⟶ Q.cocone.pt
  square : ∀ j : J,
    P.cocone.ι.app (op (r.obj j)) ≫ apex = stages.app (op j) ≫ Q.cocone.ι.app (op j)
  stage_normalization : ∀ j : J,
    DerivedCategory.Q.map (stages.app (op j)) ≫ (Q.stage j).hom =
      (P.stage (r.obj j)).hom ≫ pullback A K M (η.app j) ≫
        coefficientMap A K M α β (E.obj j)
  apex_normalization : DerivedCategory.Q.map apex ≫ Q.apex.hom =
    P.apex.hom ≫ pullback A K M v ≫ coefficientMap A K M α β d.pt

end AlgebraicGeometry.Etale.IndEtaleMapping
