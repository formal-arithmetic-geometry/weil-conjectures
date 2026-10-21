/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Topology.Stratification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.SixFunctors.ComparisonOpenTensorCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap

/-!
# Etale-to-pro-etale comparison of the direct-image projection morphism

Source: Stacks Project, Tags 09A6, 07A4 and 0E48; main-20261015 blueprint,
finite proper base change proof, paragraph (3), canonical-map transport
(blueprint: lem-sfb-projection-comparison-etale-proetale).

The two routes are components of a single natural transformation on the full
subcategory of admissible pairs. This records both their equality and its
naturality, including arbitrary morphisms in both inputs. All operations are
ordinary uncompleted constant-coefficient operations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The admissible pairs: K and K tensor p* N are bounded below; N is unrestricted.
This is a property of pairs in the existing unbounded derived categories.
Source: Stacks Tags 09A6 and 0E48; finite proper base change proof, paragraph (3)
(blueprint: lem-sfb-projection-comparison-etale-proetale). -/
def sfbProjectionComparisonAdmissible (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    ObjectProperty (Etale.DerivedCategoryModule A X × Etale.DerivedCategoryModule A Y) :=
  fun B ↦ (∃ n : ℤ, B.1.IsGE n) ∧
    ∃ n : ℤ, (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.1).obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.2)).IsGE n

/-- The common source F_Y(R_e K tensor N), functorially on admissible pairs.
Source: Stacks Tag 0E48; finite proper base change proof, paragraph (3)
(blueprint: lem-sfb-projection-comparison-etale-proetale). -/
def sfbProjectionComparisonSource (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (sfbProjectionComparisonAdmissible A p).FullSubcategory ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) :=
  (sfbProjectionComparisonAdmissible A p).ι ⋙
    Functor.uncurry.obj (Etale.derivedTensorRightDerivedLowerStar (ModuleCat.{u + 1} A) p) ⋙
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory

/-- The common target R_p(F_X K tensor v F_Y N), functorially on admissible pairs.
Source: Stacks Tag 0E48; finite proper base change proof, paragraph (3)
(blueprint: lem-sfb-projection-comparison-etale-proetale). -/
def sfbProjectionComparisonTarget (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (sfbProjectionComparisonAdmissible A p).FullSubcategory ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) :=
  (sfbProjectionComparisonAdmissible A p).ι ⋙
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.prod
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory) ⋙
    Functor.uncurry.obj
      (rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar (ModuleCat.{u + 1} A) p)

/-- The compact admissibility interface is exactly the two bounds in the node.
Source: Stacks Tags 09A6 and 0E48; finite proper base change proof, paragraph (3)
(blueprint: lem-sfb-projection-comparison-etale-proetale).
Proof: unfold the admissibility property; its two conjuncts are these two bounds. -/
theorem sfbProjectionComparisonAdmissible_iff (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (B : Etale.DerivedCategoryModule A X × Etale.DerivedCategoryModule A Y) :
    sfbProjectionComparisonAdmissible A p B ↔
      (∃ n : ℤ, B.1.IsGE n) ∧
        ∃ n : ℤ, (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.1).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.2)).IsGE n := by
  sorry

/-- The source interface denotes exactly F_Y(R_e K tensor N), on objects and maps.
Source: Stacks Tag 0E48; finite proper base change proof, paragraph (3)
(blueprint: lem-sfb-projection-comparison-etale-proetale).
Proof: unfold the source interface; it is this composite of existing functors. -/
theorem sfbProjectionComparisonSource_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    sfbProjectionComparisonSource A p =
      (sfbProjectionComparisonAdmissible A p).ι ⋙
        Functor.uncurry.obj
          (Etale.derivedTensorRightDerivedLowerStar (ModuleCat.{u + 1} A) p) ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory := by
  sorry

/-- The target interface denotes exactly R_p(F_X K tensor v F_Y N), on objects and maps.
Source: Stacks Tag 0E48; finite proper base change proof, paragraph (3)
(blueprint: lem-sfb-projection-comparison-etale-proetale).
Proof: unfold the target interface; it is this composite of existing functors. -/
theorem sfbProjectionComparisonTarget_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    sfbProjectionComparisonTarget A p =
      (sfbProjectionComparisonAdmissible A p).ι ⋙
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.prod
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory) ⋙
        Functor.uncurry.obj
          (rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar (ModuleCat.{u + 1} A) p) := by
  sorry

/-- The canonical etale and pro-etale projection morphisms agree through the
specified comparison maps, naturally in both inputs. The first component formula
is F_Y(pi_e), then b_L, then R_p(h); the second is t_Y, then b_K tensor 1,
then pi_p. Here comparisonOpenTensorIso is defined for every scheme morphism:
its hom is exactly t_X followed by 1 tensor the canonical pullback comparison.
The direct-image morphism is fixedComparisonDirectImageMatePlus included into
the unbounded categories using the standard D+ compatibility isomorphisms.
The five arrows implementing that inclusion are written out at K and L.
Thus neither comparison is an arbitrary isomorphism between the endpoints.

Source: Stacks Tags 09A6, 07A4 and 0E48; main-20261015 blueprint, finite proper
base change proof, paragraph (3)
(blueprint: lem-sfb-projection-comparison-etale-proetale).

Proof:
1. Form the ringed comparison square with horizontal maps nu_X and nu_Y and
vertical maps p_et and p_proet. The constant-section coefficient maps make the
specified pullback comparison a ringed comparison; the exchange orientation
is its inverse. Use comparison-pullback and proetale-constant-ring-map.
2. The transpose of its exchange mate at B is F_X(epsilon_B) after the inverse
pullback comparison. For B = K and B = L, the recorded direct-image-canonical-mate
has this same transpose. Injectivity of the adjunction Hom bijection identifies
the exchange components with b_K and b_L. Both are defined and invertible:
p is qcqs, A is finite, and K,L are bounded below. No bound on N is used.
3. Apply ringed-exchange-tensor-coherence to this square. Its projection maps
are precisely the counit-defined maps of projection-formula-map and
ringed-projection-mate-exact. Its tensor comparisons are the canonical ones
of ringed-topoi-derived-tensor-pullback. The last target identification is
h = (1 tensor a_N) after t_X. Substitution gives the two component formulas.
4. The same coherence theorem is natural in both inputs. The included normalized
mate is natural on D+, so restrict to the full subcategory of pairs with K,L
bounded below. The resulting common transformation has the displayed components.
No properness, constructibility, Tor amplitude, or invertibility of either
projection morphism enters this argument. -/
theorem projection_comparison_etale_proetale (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p] :
    ∃ alpha : sfbProjectionComparisonSource A p ⟶ sfbProjectionComparisonTarget A p,
      ∀ B : (sfbProjectionComparisonAdmissible A p).FullSubcategory,
        alpha.app B =
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
            (((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app
              B.obj.1).app B.obj.2) ≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
            ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.inv.app
              ⟨(((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.obj.1).obj
                  ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.obj.2)),
                B.property.2⟩) ≫
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlusCompatibility.inv.app
            ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) p).obj
              ⟨(((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.obj.1).obj
                  ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.obj.2)),
                B.property.2⟩)) ≫
          DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A p).app
            ⟨(((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.obj.1).obj
                  ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.obj.2)),
                B.property.2⟩) ≫
          (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj
              ⟨(((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.obj.1).obj
                  ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.obj.2)),
                B.property.2⟩) ≫
          (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
            ((Functor.mapDerivedCategoryPlusCompatibility
                (comparisonUpperStar (ModuleCat.{u + 1} A) X)).hom.app
              ⟨(((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj B.obj.1).obj
                  ((Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj B.obj.2)),
                B.property.2⟩) ≫
          (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
            (comparisonOpenTensorIso A p B.obj.1 B.obj.2).hom ∧
        alpha.app B =
          ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
            (ModuleCat.{u + 1} A)
            ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj B.obj.1)).app
              B.obj.2).hom ≫
          ((derivedTensor (ModuleCat.{u + 1} A) Y).map
            (
              (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
                ((Functor.rightDerivedFunctorPlusCompatibility
                    (Etale.lowerStar (ModuleCat.{u + 1} A) p)).inv.app
                  ⟨B.obj.1, B.property.1⟩) ≫
              ((Functor.mapDerivedCategoryPlusCompatibility
                  (comparisonUpperStar (ModuleCat.{u + 1} A) Y)).inv.app
                ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) p).obj
                  ⟨B.obj.1, B.property.1⟩)) ≫
              DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A p).app
                ⟨B.obj.1, B.property.1⟩) ≫
              (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
                ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj
                  ⟨B.obj.1, B.property.1⟩) ≫
              (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
                ((Functor.mapDerivedCategoryPlusCompatibility
                    (comparisonUpperStar (ModuleCat.{u + 1} A) X)).hom.app
                  ⟨B.obj.1, B.property.1⟩))).app
              ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj B.obj.2) ≫
          (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) p).app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
              B.obj.1)).app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj B.obj.2)) := by
  sorry

end AlgebraicGeometry.ProEtale
