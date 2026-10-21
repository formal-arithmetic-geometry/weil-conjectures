/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import Sheaf.AlgebraicGeometry.OpenComparisonTensorNormalization
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison

/-!
# Site transport of the open projection formula
Source: Stacks Project, `proetale.tex`, Tag 09AF, `lemma-jshriek-comparison`,
combined with `sites-cohomology.tex`, Tag 0GL1, `lemma-j-shriek-and-tensor`.
The derived statement and its K-flat normalization follow the blueprint item
`lem-pur-open-projection-site-transport` (blueprint: lem-pur-open-projection-site-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The comparison square for the canonical open projection maps, for arbitrary
unbounded derived objects. The two displayed composites use the fixed adjoint-normalized
extension comparison, the tensor comparison of exact comparison pullback, and the
exact-to-left-derived restriction comparisons.
Source: Stacks Project, proetale.tex, Tag 09AF, lemma-jshriek-comparison; and
sites-cohomology.tex, Tag 0GL1, lemma-j-shriek-and-tensor.
Proof: First apply the unit normalization of the ordinary open comparison. Replace
restriction by the canonically isomorphic inverse-image functor on both sites, and
cancel the restriction isomorphisms; this says that the inverse extension comparison
is the mate of the inverse inverse-image square. Derive this mate equality using the
termwise derived adjunctions. The mixed tensor comparison used to define the projection
map is obtained from the left-derived tensor comparison by replacing its first
left-derived restriction with exact termwise restriction. Compatibility of the
left-derived tensor comparisons with the comparison inverse-image square, followed by
these exact-to-derived isomorphisms, gives compatibility of the mixed comparisons.
Apply Adjunction.projectionMap_mate to the two derived open adjunctions with these
mixed comparisons and the comparison tensor isomorphisms. Postcompose with the tensor
of the extension comparison and cancel its inverse. Naturality and reassociation give
precisely the two composites displayed below. This argument uses no boundedness or
local freeness; it also applies to zero objects, an empty open, and the zero ring.
(blueprint: lem-pur-open-projection-comparison-square). -/
theorem openProjectionTransport_projection_square
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (F : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (B : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
        (((Etale.derivedOpenImmersionLowerShriekProjectionMap
          (ModuleCat.{u + 1} Λ) j).app F).app B) ≫
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} Λ)
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj F)).app B ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso
      ((((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _)).app F)).app _).hom =
    ((((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} Λ) j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _)).app _ ≪≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.mapIso
      (((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} Λ) F).app _) ≪≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj _).mapIso
          (((Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j) _ ≪≫
    ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).symm)).app B))).hom ≫
      ((derivedOpenImmersionLowerShriekProjectionMap (ModuleCat.{u + 1} Λ) j).app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj F)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj B) := by sorry

end AlgebraicGeometry.ProEtale
