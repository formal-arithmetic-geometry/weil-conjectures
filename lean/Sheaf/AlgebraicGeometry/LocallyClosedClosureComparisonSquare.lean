/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.Paper.ComparisonPullbackExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.CategoryTheory.DerivedExactSquare
import Sheaf.AlgebraicGeometry.DerivedImmersionComparisonNormalization

/-! # The normalized locally closed closure comparison square

Source: Weil blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
lem-weil-finite-duality-site-comparison.proof.md, second paragraph;
Stacks Tags 0GJ1, 04CA, 09AF, 099R and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square).

All composites below use the specified open comparison and the specified derived
closed counit mate. Normalized closure identifications are expressed in derived
coordinates: their restriction is the identity under the actual open units, closed
counits and pullback compositors. This normalization also characterizes the
termwise identifications uniquely, so it does not permit a different choice of map.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxRecDepth 2048

universe u uC uD vC vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale
/-- The closed-then-open extension F_e on the bounded below derived category.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
abbrev closureSquareEtaleFactor (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T) [IsOpenImmersion v] :=
  (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlus ⋙
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus

/-- The closed-then-open extension F_p on the bounded below derived category.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
abbrev closureSquareProEtaleFactor (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T) [IsOpenImmersion v] :=
  (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlus ⋙
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus

/-- The open-then-closed extension E_e.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
abbrev closureSquareEtaleClosure (A : Type (u + 1)) [CommRing A]
    {S Z T : Scheme.{u}} (u : S ⟶ Z) (i : Z ⟶ T) [IsOpenImmersion u] :=
  (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategoryPlus ⋙
    (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus

/-- The open-then-closed extension E_p.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
abbrev closureSquareProEtaleClosure (A : Type (u + 1)) [CommRing A]
    {S Z T : Scheme.{u}} (u : S ⟶ Z) (i : Z ⟶ T) [IsOpenImmersion u] :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategoryPlus ⋙
    (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus

/-- The termwise canonical open comparison o_j, with its direction fixed.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
def closureSquareOpenComparison (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus ⋙
        siteComparisonDerivedPullbackPlus X A ≅
      siteComparisonDerivedPullbackPlus U A ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- Delta is o_v followed by v_! of the specified closed mate delta_c.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
def closureSquareDelta (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] :
    closureSquareEtaleFactor A c v ⋙ siteComparisonDerivedPullbackPlus T A ≅
      siteComparisonDerivedPullbackPlus S A ⋙ closureSquareProEtaleFactor A c v :=
  Functor.isoWhiskerLeft (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlus
      (closureSquareOpenComparison A v) ≪≫
    Functor.isoWhiskerRight
      (@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A c)
        (isIso_fixedComparisonDirectImageMatePlus A c))
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus

/-- B is the specified closed mate delta_i followed by i_* of o_u.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
def closureSquareB (A : Type (u + 1)) [CommRing A] [Finite A]
    {S Z T : Scheme.{u}} (u : S ⟶ Z) (i : Z ⟶ T)
    [IsOpenImmersion u] [IsClosedImmersion i] :
    closureSquareEtaleClosure A u i ⋙ siteComparisonDerivedPullbackPlus T A ≅
      siteComparisonDerivedPullbackPlus S A ⋙ closureSquareProEtaleClosure A u i :=
  Functor.isoWhiskerLeft
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategoryPlus
      (@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A i)
        (isIso_fixedComparisonDirectImageMatePlus A i)) ≪≫
    Functor.isoWhiskerRight (closureSquareOpenComparison A u)
      (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorPlus

/-- The inverse open unit on D+, descended termwise from the sheaf unit.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
def closureSquareEtaleOpenRestriction (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus ⋙
        (Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (asIso (Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).unit).symm ≪≫
    Functor.mapDerivedCategoryPlusIdIso _

/-- The canonical pullback compositor for a specified factorization of s.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
def closureSquareEtalePullComp (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (f : S ⟶ V) (g : V ⟶ T) (s : S ⟶ T)
    (h : f ≫ g = s) :
    (Etale.upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus ⋙
        (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus :=
  Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} A) f g s h.symm

/-- The factorized restriction r_F: pullback compositor, inverse open unit, closed counit.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
def closureSquareEtaleFactorRestriction (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (s : S ⟶ T) (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] (h : c ≫ v = s) :
    closureSquareEtaleFactor A c v ⋙
        (Etale.upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ⟶ 𝟭 _ :=
  Functor.whiskerLeft (closureSquareEtaleFactor A c v)
      (closureSquareEtalePullComp A c v s h).hom ≫
    Functor.whiskerLeft (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlus
      (Functor.whiskerRight (closureSquareEtaleOpenRestriction A v).hom
        (Etale.upperStar (ModuleCat.{u + 1} A) c).mapDerivedCategoryPlus) ≫
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) c).counit

/-- The closure restriction r_E: pullback compositor, closed counit, inverse open unit.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
def closureSquareEtaleClosureRestriction (A : Type (u + 1)) [CommRing A]
    {S Z T : Scheme.{u}} (s : S ⟶ T) (u : S ⟶ Z) (i : Z ⟶ T)
    [IsOpenImmersion u] [IsClosedImmersion i] (h : u ≫ i = s) :
    closureSquareEtaleClosure A u i ⋙
        (Etale.upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ⟶ 𝟭 _ :=
  Functor.whiskerLeft (closureSquareEtaleClosure A u i)
      (closureSquareEtalePullComp A u i s h).hom ≫
    Functor.whiskerLeft
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategoryPlus
      (Functor.whiskerRight
        (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) i).counit
        (Etale.upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategoryPlus) ≫
    (closureSquareEtaleOpenRestriction A u).hom

/-- The inverse open unit on D+, descended termwise from the sheaf unit.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
def closureSquareProEtaleOpenRestriction (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus ≅ 𝟭 _ :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (asIso (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).unit).symm ≪≫
    Functor.mapDerivedCategoryPlusIdIso _

/-- The canonical pullback compositor for a specified factorization of s.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
def closureSquareProEtalePullComp (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (f : S ⟶ V) (g : V ⟶ T) (s : S ⟶ T)
    (h : f ≫ g = s) :
    (upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus :=
  Functor.mapDerivedCategoryPlusNatIso
      (upperStarCongr (ModuleCat.{u + 1} A) h.symm ≪≫
        upperStarComp (ModuleCat.{u + 1} A) f g) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The factorized restriction r_F: pullback compositor, inverse open unit, closed counit.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
def closureSquareProEtaleFactorRestriction (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (s : S ⟶ T) (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v] (h : c ≫ v = s) :
    closureSquareProEtaleFactor A c v ⋙
        (upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ⟶ 𝟭 _ :=
  Functor.whiskerLeft (closureSquareProEtaleFactor A c v)
      (closureSquareProEtalePullComp A c v s h).hom ≫
    Functor.whiskerLeft (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlus
      (Functor.whiskerRight (closureSquareProEtaleOpenRestriction A v).hom
        (upperStar (ModuleCat.{u + 1} A) c).mapDerivedCategoryPlus) ≫
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) c).counit

/-- The closure restriction r_E: pullback compositor, closed counit, inverse open unit.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
def closureSquareProEtaleClosureRestriction (A : Type (u + 1)) [CommRing A]
    {S Z T : Scheme.{u}} (s : S ⟶ T) (u : S ⟶ Z) (i : Z ⟶ T)
    [IsOpenImmersion u] [IsClosedImmersion i] (h : u ≫ i = s) :
    closureSquareProEtaleClosure A u i ⋙
        (upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ⟶ 𝟭 _ :=
  Functor.whiskerLeft (closureSquareProEtaleClosure A u i)
      (closureSquareProEtalePullComp A u i s h).hom ≫
    Functor.whiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) u).mapDerivedCategoryPlus
      (Functor.whiskerRight
        (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) i).counit
        (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategoryPlus) ≫
    (closureSquareProEtaleOpenRestriction A u).hom

/-- The canonical image factor of an immersion into a Noetherian scheme is open.
This is existing image geometry, using the induced Noetherian topology on the source.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
instance closureSquareImageOpen {S T : Scheme.{u}} (s : S ⟶ T)
    [IsImmersion s] [IsNoetherian T] : IsOpenImmersion s.toImage :=
  letI : TopologicalSpace.NoetherianSpace S := s.isEmbedding.isInducing.noetherianSpace
  inferInstance

/-- Identity normalization of q_e through the actual restriction maps.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
def closureSquareEtaleNormalized (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} [IsNoetherian T] (s : S ⟶ T) [IsImmersion s]
    (c : S ⟶ V) (v : V ⟶ T) [IsClosedImmersion c] [IsOpenImmersion v]
    (h : c ≫ v = s)
    (q : closureSquareEtaleFactor A c v ≅
      closureSquareEtaleClosure A s.toImage s.imageι) : Prop :=
  Functor.whiskerRight q.hom (Etale.upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ≫
      closureSquareEtaleClosureRestriction A s s.toImage s.imageι s.toImage_imageι =
    closureSquareEtaleFactorRestriction A s c v h

/-- Identity normalization of q_p through the actual restriction maps.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
def closureSquareProEtaleNormalized (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} [IsNoetherian T] (s : S ⟶ T) [IsImmersion s]
    (c : S ⟶ V) (v : V ⟶ T) [IsClosedImmersion c] [IsOpenImmersion v]
    (h : c ≫ v = s)
    (q : closureSquareProEtaleFactor A c v ≅
      closureSquareProEtaleClosure A s.toImage s.imageι) : Prop :=
  Functor.whiskerRight q.hom (upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ≫
      closureSquareProEtaleClosureRestriction A s s.toImage s.imageι s.toImage_imageι =
    closureSquareProEtaleFactorRestriction A s c v h

/-- Change of factorization through the one common closure, t = q followed by inverse q'.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
def closureSquareChange {C : Type uC} {D : Type uD}
    [Category.{vC} C] [Category.{vD} D]
    {F F' E : C ⥤ D} (q : F ≅ E) (q' : F' ≅ E) : F ≅ F' :=
  q ≪≫ q'.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem closure_upper_unit (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) U).map
      ((Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).unit.app F) ≫
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) j).inv.app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F) ≫
    (upperStar (ModuleCat.{u + 1} A) j).map
      ((openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} A) j).hom.app F) =
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F) := by
  have h := (openComparison_unit_normalization A j).2 F
  change _ ≫ (openComparisonRestrictionIso A j).hom.app _ ≫ _ = _ at h
  simp only [openComparisonRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  let B := ModuleCat.{u + 1} A
  have he : (Etale.openImmersionLowerShriekUpperStarAdjunction B j).unit.app F =
      (Etale.openImmersionLowerShriekAdjunction B j).unit.app F ≫
      (Etale.upperStarIsoOpenImmersionRestriction B j).inv.app
        ((Etale.openImmersionLowerShriek B j).obj F) := rfl
  have hp : (openImmersionLowerShriekUpperStarAdjunction B j).unit.app
      ((comparisonUpperStar B U).obj F) =
      (openImmersionLowerShriekAdjunction B j).unit.app
        ((comparisonUpperStar B U).obj F) ≫
      (upperStarIsoOpenImmersionRestriction B j).inv.app _ := rfl
  rw [he, hp, Functor.map_comp]
  rw [← cancel_mono ((upperStarIsoOpenImmersionRestriction B j).hom.app _)]
  dsimp only [B, Functor.comp_obj]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hn := (upperStarIsoOpenImmersionRestriction B j).hom.naturality
    ((openImmersionLowerShriekComparisonUpperStarIso B j).hom.app F)
  dsimp only [B, Functor.comp_obj] at hn
  erw [hn]
  exact h
set_option backward.isDefEq.respectTransparency false in
private theorem closure_derived_unit (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let B := ModuleCat.{u + 1} A
    let a := (comparisonUpperStarCompUpperStarIso B j).symm
    let e := openImmersionLowerShriekComparisonUpperStarIso B j
    (comparisonUpperStar B U).mapDerivedCategory.map
      ((Etale.openImmersionLowerShriekUpperStarAdjunction B j).mapDerivedCategoryAdjunction.unit.app
          K) ≫
    (Functor.mapDerivedCategorySquareIso a).hom.app
      ((Etale.openImmersionLowerShriek B j).mapDerivedCategory.obj K) ≫
    (upperStar B j).mapDerivedCategory.map
      ((Functor.mapDerivedCategorySquareIso e).hom.app K) =
    (openImmersionLowerShriekUpperStarAdjunction B j).mapDerivedCategoryAdjunction.unit.app
      ((comparisonUpperStar B U).mapDerivedCategory.obj K) := by
  dsimp only
  let B := ModuleCat.{u + 1} A
  let e := openImmersionLowerShriekComparisonUpperStarIso B j
  let a := (comparisonUpperStarCompUpperStarIso B j).symm
  have hu : ∀ F,
      (openImmersionLowerShriekUpperStarAdjunction B j).unit.app
          ((comparisonUpperStar B U).obj F) ≫
        (upperStar B j).map (e.inv.app F) =
      (comparisonUpperStar B U).map
          ((Etale.openImmersionLowerShriekUpperStarAdjunction B j).unit.app F) ≫
        a.hom.app ((Etale.openImmersionLowerShriek B j).obj F) := by
    intro F
    rw [← closure_upper_unit A j F]
    dsimp only [B, e, a]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have h := Adjunction.mapDerivedCategoryAdjunction_mate
    (Etale.openImmersionLowerShriekUpperStarAdjunction B j)
    (openImmersionLowerShriekUpperStarAdjunction B j) a e.symm hu K
  have hs : Functor.mapDerivedCategorySquareIso e.symm =
      (Functor.mapDerivedCategorySquareIso e).symm := by
    apply Iso.ext
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      Iso.trans_inv, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  rw [hs] at h
  dsimp only [B, e, a] at h
  rw [← reassoc_of% h, ← Functor.map_comp]
  simp only [Iso.symm_hom, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
private theorem closure_inclusion_map {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map f) =
      F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem closure_inclusion_comp_inv {C D E : Type*}
    [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso F G).inv.app K) =
      (Functor.mapDerivedCategoryCompIso F G).inv.app K.obj := by
  change (DerivedCategory.Plus.ι.mapIso
    ((Functor.mapDerivedCategoryPlusCompIso F G).app K)).inv =
      ((Functor.mapDerivedCategoryCompIso F G).app K.obj).inv
  congr 1
  apply Iso.ext
  exact Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app F G K

set_option backward.isDefEq.respectTransparency false in
private theorem closure_plus_unit (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let B := ModuleCat.{u + 1} A
    (comparisonUpperStar B U).mapDerivedCategoryPlus.map
      ((Etale.openImmersionLowerShriekUpperStarAdjunction
        B j).mapDerivedCategoryPlusAdjunction.unit.app K) ≫
    (fixedComparisonPullbackPlus A j).hom.app
      ((Etale.openImmersionLowerShriek B j).mapDerivedCategoryPlus.obj K) ≫
    (upperStar B j).mapDerivedCategoryPlus.map
      ((closureSquareOpenComparison A j).hom.app K) =
    (openImmersionLowerShriekUpperStarAdjunction B j).mapDerivedCategoryPlusAdjunction.unit.app
      ((comparisonUpperStar B U).mapDerivedCategoryPlus.obj K) := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := closure_derived_unit A j K.obj
  simp only [Functor.map_comp, closure_inclusion_map,
    fixedComparisonPullbackPlus, closureSquareOpenComparison, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, closure_inclusion_comp_inv,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Adjunction.mapDerivedCategoryPlusAdjunction,
    Adjunction.map_restrictFullyFaithful_unit_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app] at h ⊢
  repeat erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simpa only [Category.comp_id, Functor.comp_obj, Functor.mapDerivedCategoryPlus,
    ObjectProperty.lift, DerivedCategory.Plus.ι, ObjectProperty.ι, inducedFunctor,
    Functor.id_obj] using h

set_option backward.isDefEq.respectTransparency false in
private theorem closure_descent_symm
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    (Functor.mapDerivedCategoryPlusNatIso e.symm).hom =
      (Functor.mapDerivedCategoryPlusNatIso e).inv := by
  apply NatTrans.ext
  funext X
  apply DerivedCategory.Plus.ι.map_injective
  rw [Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.mapDerivedCategoryNatIso_symm]
  have h : DerivedCategory.Plus.ι.mapIso
      ((Functor.mapDerivedCategoryPlusNatIso e).app X) =
      (Functor.mapDerivedCategoryNatIso e).app X.obj :=
    Iso.ext (Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app e X)
  exact (congrArg Iso.inv h).symm

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

-- The descended ordinary unit is the unit of the exact derived adjunction.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closure_unit_descent
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ X : C, PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
    [∀ X : C, PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {R : D ⥤ C} [F.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (adj : F ⊣ R) [IsIso adj.unit] :
    adj.mapDerivedCategoryPlusAdjunction.unit =
      (Functor.mapDerivedCategoryPlusIdIso C).inv ≫
        (Functor.mapDerivedCategoryPlusNatIso (asIso adj.unit)).hom ≫
        (Functor.mapDerivedCategoryPlusCompIso F R).hom := by
  let : PreservesFiniteLimits (F ⋙ R) := comp_preservesFiniteLimits F R
  let : PreservesFiniteColimits (F ⋙ R) := comp_preservesFiniteColimits F R
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C)
  intro K
  rw [← cancel_mono (R.mapDerivedCategoryPlus.map
    (F.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      R.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K))]
  rw [Adjunction.mapDerivedCategoryPlusAdjunction_unit_app_fac]
  simp only [NatTrans.comp_app, Category.assoc,
    Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh, asIso_hom]
  rw [← Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh,
    Iso.inv_hom_id_app_assoc]
  congr 1
  apply (HomotopyCategory.Plus.ι C).map_injective
  rw [Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app,
    NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  change (adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app K.obj =
    (NatTrans.mapHomotopyCategory adj.unit (ComplexShape.up ℤ)).app K.obj
  obtain ⟨X, hX⟩ := HomotopyCategory.quotient_obj_surjective K.obj
  rw [← hX, Adjunction.mapHomotopyCategory_unit_app_quotient]
  rfl

-- Restriction of the open comparison is the identity in the specified unit coordinates.
set_option backward.isDefEq.respectTransparency false in
private theorem closure_open_restriction (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (fixedComparisonPullbackPlus A j).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j
          ).mapDerivedCategoryPlus.obj L) ≫
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.map
        ((closureSquareOpenComparison A j).hom.app L) ≫
      (closureSquareProEtaleOpenRestriction A j).hom.app
        ((siteComparisonDerivedPullbackPlus U A).obj L) =
      (siteComparisonDerivedPullbackPlus U A).map
        ((closureSquareEtaleOpenRestriction A j).hom.app L) := by
  let B := ModuleCat.{u + 1} A
  have hu := closure_plus_unit A j L
  have he := closure_unit_descent (Etale.openImmersionLowerShriekUpperStarAdjunction B j)
  have hp := closure_unit_descent (openImmersionLowerShriekUpperStarAdjunction B j)
  have hrE : (closureSquareEtaleOpenRestriction A j).hom ≫
      (Etale.openImmersionLowerShriekUpperStarAdjunction B j
        ).mapDerivedCategoryPlusAdjunction.unit = 𝟙 _ := by
    rw [he]
    apply NatTrans.ext
    funext K
    simp only [B, closureSquareEtaleOpenRestriction, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc]
    simp only [closure_descent_symm, Iso.hom_inv_id_app_assoc,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, NatTrans.id_app]
  have hrP : (openImmersionLowerShriekUpperStarAdjunction B j
      ).mapDerivedCategoryPlusAdjunction.unit ≫
      (closureSquareProEtaleOpenRestriction A j).hom = 𝟙 _ := by
    rw [hp]
    apply NatTrans.ext
    funext K
    simp only [B, closureSquareProEtaleOpenRestriction, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc]
    simp only [closure_descent_symm, Iso.hom_inv_id_app_assoc,
      Iso.inv_hom_id_app, NatTrans.id_app]
  have eE := congr_app hrE L
  have eP := congr_app hrP ((siteComparisonDerivedPullbackPlus U A).obj L)
  simp only [NatTrans.comp_app, NatTrans.id_app] at eE eP
  have h := congrArg (fun f ↦
    (siteComparisonDerivedPullbackPlus U A).map
      ((closureSquareEtaleOpenRestriction A j).hom.app L) ≫ f ≫
    (closureSquareProEtaleOpenRestriction A j).hom.app
      ((siteComparisonDerivedPullbackPlus U A).obj L)) hu
  simp only [← Functor.map_comp_assoc, Category.assoc] at h
  erw [eE, CategoryTheory.Functor.map_id, Category.id_comp, eP, Category.comp_id] at h
  exact h

-- The one comparison for s agrees with the successive comparisons for its factors.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closure_pullback_comp (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} (f : S ⟶ V) (g : V ⟶ T) (s : S ⟶ T)
    (h : f ≫ g = s)
    (L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (fixedComparisonPullbackPlus A s).hom.app L ≫
        (closureSquareProEtalePullComp A f g s h).hom.app
          ((siteComparisonDerivedPullbackPlus T A).obj L) =
      (siteComparisonDerivedPullbackPlus S A).map
          ((closureSquareEtalePullComp A f g s h).hom.app L) ≫
        (fixedComparisonPullbackPlus A f).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.obj L) ≫
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.map
          ((fixedComparisonPullbackPlus A g).hom.app L) := by
  subst s
  let B := ModuleCat.{u + 1} A
  have hs (M : Sheaf T.smallEtaleTopology B) :=
    ((supportSiteComparison_pullback_coherent.{u}).2.2 A).2.1 S V T f g M
  have hq (M : Sheaf T.smallEtaleTopology B) :
      (comparisonUpperStarCompUpperStarIso B (f ≫ g)).hom.app M ≫
          (comparisonUpperStar B S).map ((Etale.upperStarComp B f g).hom.app M) =
        (upperStarComp B f g).hom.app ((comparisonUpperStar B T).obj M) ≫
          (upperStar B f).map ((comparisonUpperStarCompUpperStarIso B g).hom.app M) ≫
          (comparisonUpperStarCompUpperStarIso B f).hom.app
            ((Etale.upperStar B g).obj M) := by
    have hm := hs M
    have hec : etaleComparisonComp B f g = Etale.upperStarComp B f g := by
      unfold etaleComparisonComp Etale.upperStarComp
      rfl
    have hpc : proEtaleComparisonComp B f g = upperStarComp B f g := by
      unfold proEtaleComparisonComp upperStarComp
      rfl
    rw [hec, hpc] at hm
    change (comparisonUpperStar B S).map ((Etale.upperStarComp B f g).hom.app M) ≫
        (comparisonUpperStarCompUpperStarIso B f).inv.app ((Etale.upperStar B g).obj M) ≫
        (upperStar B f).map ((comparisonUpperStarCompUpperStarIso B g).inv.app M) =
      (comparisonUpperStarCompUpperStarIso B (f ≫ g)).inv.app M ≫
        (upperStarComp B f g).hom.app ((comparisonUpperStar B T).obj M) at hm
    apply (cancel_epi ((comparisonUpperStarCompUpperStarIso B (f ≫ g)).inv.app M)).1
    rw [Iso.inv_hom_id_app_assoc, ← reassoc_of% hm,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app,
      Category.comp_id]
  have hd := Functor.mapDerivedCategoryPlusSquareIso_comp
    (Etale.upperStar B g) (Etale.upperStar B f) (Etale.upperStar B (f ≫ g))
    (upperStar B g) (upperStar B f) (upperStar B (f ≫ g))
    (comparisonUpperStar B T) (comparisonUpperStar B V) (comparisonUpperStar B S)
    (comparisonUpperStarCompUpperStarIso B g) (comparisonUpperStarCompUpperStarIso B f)
    (comparisonUpperStarCompUpperStarIso B (f ≫ g))
    (Etale.upperStarComp B f g) (upperStarComp B f g) hq L
  have hi {X Y : Scheme.{u}} (k : X ⟶ Y) :
      (Functor.mapDerivedCategoryPlusSquareIso (comparisonUpperStar B Y) (upperStar B k)
        (Etale.upperStar B k) (comparisonUpperStar B X)
        (comparisonUpperStarCompUpperStarIso B k)).hom =
      (fixedComparisonPullbackPlus A k).inv := by
    have hs :
        (Functor.mapDerivedCategoryPlusNatIso
          (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) k).symm).inv =
        (Functor.mapDerivedCategoryPlusNatIso
          (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) k)).hom :=
      (closure_descent_symm
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) k).symm).symm
    dsimp only [B]
    simp only [Functor.mapDerivedCategoryPlusSquareIso, fixedComparisonPullbackPlus,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
    rw [hs]
  rw [hi, hi, hi] at hd
  change (fixedComparisonPullbackPlus A (f ≫ g)).inv.app L ≫
      (siteComparisonDerivedPullbackPlus S A).map
        ((closureSquareEtalePullComp A f g (f ≫ g) rfl).hom.app L) =
    (closureSquareProEtalePullComp A f g (f ≫ g) rfl).hom.app
      ((siteComparisonDerivedPullbackPlus T A).obj L) ≫
      (upperStar B f).mapDerivedCategoryPlus.map
        ((fixedComparisonPullbackPlus A g).inv.app L) ≫
      (fixedComparisonPullbackPlus A f).inv.app
        ((Etale.upperStar B g).mapDerivedCategoryPlus.obj L) at hd
  dsimp only [B] at hd
  apply (cancel_epi ((fixedComparisonPullbackPlus A (f ≫ g)).inv.app L)).1
  rw [Iso.inv_hom_id_app_assoc, reassoc_of% hd,
    Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

-- Pasting two restriction-normalized comparison squares preserves normalization.
set_option backward.isDefEq.respectTransparency false in
private theorem closure_paste_restriction
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (C₀ : A₀ ⥤ B₀) (C₁ : A₁ ⥤ B₁) (C₂ : A₂ ⥤ B₂)
    (E₁ : A₀ ⥤ A₁) (E₂ : A₁ ⥤ A₂) (P₁ : A₁ ⥤ A₀) (P₂ : A₂ ⥤ A₁)
    (F₁ : B₀ ⥤ B₁) (F₂ : B₁ ⥤ B₂) (Q₁ : B₁ ⥤ B₀) (Q₂ : B₂ ⥤ B₁)
    (P : A₂ ⥤ A₀) (Q : B₂ ⥤ B₀)
    (k : P ≅ P₂ ⋙ P₁) (l : Q ≅ Q₂ ⋙ Q₁)
    (a : P ⋙ C₀ ≅ C₂ ⋙ Q)
    (a₁ : P₁ ⋙ C₀ ≅ C₁ ⋙ Q₁) (a₂ : P₂ ⋙ C₁ ≅ C₂ ⋙ Q₂)
    (x₁ : E₁ ⋙ C₁ ≅ C₀ ⋙ F₁) (x₂ : E₂ ⋙ C₂ ≅ C₁ ⋙ F₂)
    (r₁ : E₁ ⋙ P₁ ⟶ 𝟭 _) (r₂ : E₂ ⋙ P₂ ⟶ 𝟭 _)
    (t₁ : F₁ ⋙ Q₁ ⟶ 𝟭 _) (t₂ : F₂ ⋙ Q₂ ⟶ 𝟭 _)
    (ha : ∀ M, a.hom.app M ≫ l.hom.app (C₂.obj M) =
      C₀.map (k.hom.app M) ≫ a₁.hom.app (P₂.obj M) ≫ Q₁.map (a₂.hom.app M))
    (hx₁ : ∀ L, a₁.hom.app (E₁.obj L) ≫ Q₁.map (x₁.hom.app L) ≫
      t₁.app (C₀.obj L) = C₀.map (r₁.app L))
    (hx₂ : ∀ M, a₂.hom.app (E₂.obj M) ≫ Q₂.map (x₂.hom.app M) ≫
      t₂.app (C₁.obj M) = C₁.map (r₂.app M)) (L : A₀) :
    a.hom.app (E₂.obj (E₁.obj L)) ≫
        Q.map (x₂.hom.app (E₁.obj L) ≫ F₂.map (x₁.hom.app L)) ≫
        l.hom.app (F₂.obj (F₁.obj (C₀.obj L))) ≫
        Q₁.map (t₂.app (F₁.obj (C₀.obj L))) ≫ t₁.app (C₀.obj L) =
      C₀.map (k.hom.app (E₂.obj (E₁.obj L)) ≫ P₁.map (r₂.app (E₁.obj L)) ≫
        r₁.app L) := by
  rw [reassoc_of% l.hom.naturality
    (x₂.hom.app (E₁.obj L) ≫ F₂.map (x₁.hom.app L))]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% ha]
  have ht := congrArg Q₁.map (t₂.naturality (x₁.hom.app L))
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at ht
  rw [reassoc_of% ht]
  have h₂ := congrArg Q₁.map (hx₂ (E₁.obj L))
  simp only [Functor.map_comp] at h₂
  rw [reassoc_of% h₂]
  rw [← reassoc_of% a₁.hom.naturality (r₂.app (E₁.obj L))]
  rw [hx₁]

-- A left adjoint detects morphisms between objects in its right adjoint's image.
private theorem closure_right_image_injective
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {X Y : D} {f g : R.obj X ⟶ R.obj Y}
    (h : L.map f = L.map g) : f = g := by
  have hf := adj.unit.naturality f
  have hg := adj.unit.naturality g
  simp only [Functor.id_map, Functor.comp_map] at hf hg
  have hi : f ≫ adj.unit.app (R.obj Y) = g ≫ adj.unit.app (R.obj Y) := by
    rw [hf, hg, h]
  have hi' := congrArg (fun z ↦ z ≫ R.map (adj.counit.app Y)) hi
  simpa only [Category.assoc, adj.right_triangle_components, Category.comp_id] using hi'

-- A right adjoint detects morphisms between objects in its left adjoint's image.
private theorem closure_left_image_injective
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {X Y : C} {f g : L.obj X ⟶ L.obj Y}
    (h : R.map f = R.map g) : f = g := by
  apply (adj.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, h]

-- Restriction detects endomorphisms of the closed-then-open extension.
set_option backward.isDefEq.respectTransparency false in
private theorem closure_factor_injective (A : Type (u + 1)) [CommRing A]
    {S V T : Scheme.{u}} (c : S ⟶ V) (v : V ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v]
    (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)))
    {f g : (closureSquareProEtaleFactor A c v).obj L ⟶
      (closureSquareProEtaleFactor A c v).obj L}
    (h : (upperStar (ModuleCat.{u + 1} A) c).mapDerivedCategoryPlus.map
      ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus.map f) =
      (upperStar (ModuleCat.{u + 1} A) c).mapDerivedCategoryPlus.map
      ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus.map g)) : f = g := by
  let B := ModuleCat.{u + 1} A
  let adj := (openImmersionLowerShriekUpperStarAdjunction B v
    ).mapDerivedCategoryPlusAdjunction
  let e := closureSquareProEtaleOpenRestriction A v
  let Z := (lowerStar B c).rightDerivedFunctorPlus.obj L
  have hf : e.inv.app Z ≫ (upperStar B v).mapDerivedCategoryPlus.map f ≫ e.hom.app Z =
      e.inv.app Z ≫ (upperStar B v).mapDerivedCategoryPlus.map g ≫ e.hom.app Z := by
    apply closure_right_image_injective (derivedUpperStarLowerStarAdjunctionPlus B c)
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun z ↦ (upperStar B c).mapDerivedCategoryPlus.map (e.inv.app Z) ≫ z ≫
        (upperStar B c).mapDerivedCategoryPlus.map (e.hom.app Z)) h
  apply closure_left_image_injective adj
  apply (cancel_epi (e.inv.app Z)).1
  apply (cancel_mono (e.hom.app Z)).1
  simpa only [Category.assoc] using hf

-- Restriction and its invertible normalization determine a comparison square.
set_option backward.isDefEq.respectTransparency false in
private theorem closure_square_of_restriction
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (U : C ⥤ C') (V : D ⥤ D') (P : D ⥤ C) (Q : D' ⥤ C')
    (F E : C ⥤ D) (F' E' : C' ⥤ D')
    (a : P ⋙ U ≅ V ⋙ Q) (d : F ⋙ V ≅ U ⋙ F') (b : E ⋙ V ≅ U ⋙ E')
    (qe : F ≅ E) (qp : F' ≅ E')
    (rF : F ⋙ P ⟶ 𝟭 _) (rE : E ⋙ P ⟶ 𝟭 _)
    (tF : F' ⋙ Q ⟶ 𝟭 _) (tE : E' ⋙ Q ⟶ 𝟭 _)
    (he : Functor.whiskerRight qe.hom P ≫ rE = rF)
    (hp : Functor.whiskerRight qp.hom Q ≫ tE = tF)
    (hd : Functor.whiskerLeft F a.hom ≫ Functor.whiskerRight d.hom Q ≫
      Functor.whiskerLeft U tF = Functor.whiskerRight rF U)
    (hb : Functor.whiskerLeft E a.hom ≫ Functor.whiskerRight b.hom Q ≫
      Functor.whiskerLeft U tE = Functor.whiskerRight rE U)
    (hi : ∀ L : C, IsIso (tF.app (U.obj L)))
    (hinj : ∀ L : C, ∀ f g : F'.obj (U.obj L) ⟶ F'.obj (U.obj L),
      Q.map f = Q.map g → f = g) :
    d.hom ≫ Functor.whiskerLeft U qp.hom = Functor.whiskerRight qe.hom V ≫ b.hom := by
  apply NatTrans.ext
  funext L
  have hpn := congr_app hp (U.obj L)
  have hen := congr_app he L
  have hdn := congr_app hd L
  have hbn := congr_app hb L
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    at hpn hen hdn hbn ⊢
  have := hi L
  have : IsIso (tE.app (U.obj L)) := by
    have : IsIso (Q.map (qp.hom.app (U.obj L)) ≫ tE.app (U.obj L)) := by
      rw [hpn]
      infer_instance
    exact IsIso.of_isIso_comp_left (Q.map (qp.hom.app (U.obj L))) _
  have hr : Q.map (d.hom.app L ≫ qp.hom.app (U.obj L)) =
      Q.map (V.map (qe.hom.app L) ≫ b.hom.app L) := by
    apply (cancel_epi (a.hom.app (F.obj L))).1
    apply (cancel_mono (tE.app (U.obj L))).1
    simp only [Functor.map_comp, Category.assoc]
    rw [hpn, hdn]
    have hn := a.hom.naturality (qe.hom.app L)
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn, hbn, ← U.map_comp, hen]
  have hh := hinj L
    (d.inv.app L ≫ (d.hom.app L ≫ qp.hom.app (U.obj L)) ≫ qp.inv.app (U.obj L))
    (d.inv.app L ≫ (V.map (qe.hom.app L) ≫ b.hom.app L) ≫ qp.inv.app (U.obj L))
    (by simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun z ↦ Q.map (d.inv.app L) ≫ z ≫ Q.map (qp.inv.app (U.obj L))) hr)
  apply (cancel_epi (d.inv.app L)).1
  apply (cancel_mono (qp.inv.app (U.obj L))).1
  simpa only [Category.assoc] using hh

/-- The specified closure square, together with both restriction-normalization equations.
Source: blueprint main-20261015, locally closed comparison sentence; Stacks 09AF, 099R,
0B65, 0GJ1 and 04CA
(blueprint: lem-sf-locally-closed-closure-comparison-square).

Proof: the open-unit normalization and the specified closed-mate counit equation
paste to give the two restriction identities. The pullback-comparison composition law
identifies their composite inverse images with the fixed pullback along s. Restricting
the proposed square then gives equality by the hypotheses he and hp and naturality.
The factor restriction is invertible: the open unit is invertible and the closed
counit is invertible over the Noetherian open intermediate scheme. Conjugate the two
maps to endomorphisms of the closed-then-open extension. The two adjunction triangle
identities show that successive restriction detects these endomorphisms; cancel the
conjugations to obtain the square. -/
theorem locallyClosed_closure_comparison_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V T : Scheme.{u}} [IsNoetherian T] (s : S ⟶ T) [IsImmersion s]
    (c : S ⟶ V) (v : V ⟶ T) [IsClosedImmersion c] [IsOpenImmersion v]
    (h : c ≫ v = s)
    (qe : closureSquareEtaleFactor A c v ≅ closureSquareEtaleClosure A s.toImage s.imageι)
    (qp : closureSquareProEtaleFactor A c v ≅
      closureSquareProEtaleClosure A s.toImage s.imageι)
    (he : closureSquareEtaleNormalized A s c v h qe)
    (hp : closureSquareProEtaleNormalized A s c v h qp) :
    ((closureSquareDelta A c v).hom ≫
        Functor.whiskerLeft (siteComparisonDerivedPullbackPlus S A) qp.hom =
      Functor.whiskerRight qe.hom (siteComparisonDerivedPullbackPlus T A) ≫
        (closureSquareB A s.toImage s.imageι).hom) ∧
    (Functor.whiskerLeft (closureSquareEtaleFactor A c v)
          (fixedComparisonPullbackPlus A s).hom ≫
        Functor.whiskerRight (closureSquareDelta A c v).hom
          (upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ≫
        Functor.whiskerLeft (siteComparisonDerivedPullbackPlus S A)
          (closureSquareProEtaleFactorRestriction A s c v h) =
      Functor.whiskerRight (closureSquareEtaleFactorRestriction A s c v h)
        (siteComparisonDerivedPullbackPlus S A)) ∧
    (Functor.whiskerLeft (closureSquareEtaleClosure A s.toImage s.imageι)
          (fixedComparisonPullbackPlus A s).hom ≫
        Functor.whiskerRight (closureSquareB A s.toImage s.imageι).hom
          (upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ≫
        Functor.whiskerLeft (siteComparisonDerivedPullbackPlus S A)
          (closureSquareProEtaleClosureRestriction A s s.toImage s.imageι s.toImage_imageι) =
      Functor.whiskerRight
        (closureSquareEtaleClosureRestriction A s s.toImage s.imageι s.toImage_imageι)
        (siteComparisonDerivedPullbackPlus S A)) := by
  have hF :
      Functor.whiskerLeft (closureSquareEtaleFactor A c v)
          (fixedComparisonPullbackPlus A s).hom ≫
        Functor.whiskerRight (closureSquareDelta A c v).hom
          (upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ≫
        Functor.whiskerLeft (siteComparisonDerivedPullbackPlus S A)
          (closureSquareProEtaleFactorRestriction A s c v h) =
      Functor.whiskerRight (closureSquareEtaleFactorRestriction A s c v h)
        (siteComparisonDerivedPullbackPlus S A) := by
    apply NatTrans.ext
    funext L
    exact closure_paste_restriction
      (siteComparisonDerivedPullbackPlus S A) (siteComparisonDerivedPullbackPlus V A)
      (siteComparisonDerivedPullbackPlus T A)
      (Etale.lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlus
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus
      (Etale.upperStar (ModuleCat.{u + 1} A) c).mapDerivedCategoryPlus
      (Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus
      (lowerStar (ModuleCat.{u + 1} A) c).rightDerivedFunctorPlus
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus
      (upperStar (ModuleCat.{u + 1} A) c).mapDerivedCategoryPlus
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus
      (Etale.upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus
      (upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus
      (closureSquareEtalePullComp A c v s h) (closureSquareProEtalePullComp A c v s h)
      (fixedComparisonPullbackPlus A s) (fixedComparisonPullbackPlus A c)
      (fixedComparisonPullbackPlus A v)
      (@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A c)
        (isIso_fixedComparisonDirectImageMatePlus A c))
      (closureSquareOpenComparison A v)
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) c).counit
      (closureSquareEtaleOpenRestriction A v).hom
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) c).counit
      (closureSquareProEtaleOpenRestriction A v).hom
      (closure_pullback_comp A c v s h)
      (fixedComparisonDirectImageMatePlus_counit A c) (closure_open_restriction A v) L
  have hE :
      Functor.whiskerLeft (closureSquareEtaleClosure A s.toImage s.imageι)
          (fixedComparisonPullbackPlus A s).hom ≫
        Functor.whiskerRight (closureSquareB A s.toImage s.imageι).hom
          (upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ≫
        Functor.whiskerLeft (siteComparisonDerivedPullbackPlus S A)
          (closureSquareProEtaleClosureRestriction A s s.toImage s.imageι s.toImage_imageι) =
      Functor.whiskerRight
        (closureSquareEtaleClosureRestriction A s s.toImage s.imageι s.toImage_imageι)
        (siteComparisonDerivedPullbackPlus S A) := by
    apply NatTrans.ext
    funext L
    exact closure_paste_restriction
      (siteComparisonDerivedPullbackPlus S A)
      (siteComparisonDerivedPullbackPlus s.image A) (siteComparisonDerivedPullbackPlus T A)
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage).mapDerivedCategoryPlus
      (Etale.lowerStar (ModuleCat.{u + 1} A) s.imageι).rightDerivedFunctorPlus
      (Etale.upperStar (ModuleCat.{u + 1} A) s.toImage).mapDerivedCategoryPlus
      (Etale.upperStar (ModuleCat.{u + 1} A) s.imageι).mapDerivedCategoryPlus
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage).mapDerivedCategoryPlus
      (lowerStar (ModuleCat.{u + 1} A) s.imageι).rightDerivedFunctorPlus
      (upperStar (ModuleCat.{u + 1} A) s.toImage).mapDerivedCategoryPlus
      (upperStar (ModuleCat.{u + 1} A) s.imageι).mapDerivedCategoryPlus
      (Etale.upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus
      (upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus
      (closureSquareEtalePullComp A s.toImage s.imageι s s.toImage_imageι)
      (closureSquareProEtalePullComp A s.toImage s.imageι s s.toImage_imageι)
      (fixedComparisonPullbackPlus A s) (fixedComparisonPullbackPlus A s.toImage)
      (fixedComparisonPullbackPlus A s.imageι)
      (closureSquareOpenComparison A s.toImage)
      (@asIso _ _ _ _ (fixedComparisonDirectImageMatePlus A s.imageι)
        (isIso_fixedComparisonDirectImageMatePlus A s.imageι))
      (closureSquareEtaleOpenRestriction A s.toImage).hom
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) s.imageι).counit
      (closureSquareProEtaleOpenRestriction A s.toImage).hom
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) s.imageι).counit
      (closure_pullback_comp A s.toImage s.imageι s s.toImage_imageι)
      (closure_open_restriction A s.toImage)
      (fixedComparisonDirectImageMatePlus_counit A s.imageι) L
  refine ⟨?_, hF, hE⟩
  apply closure_square_of_restriction
    (siteComparisonDerivedPullbackPlus S A) (siteComparisonDerivedPullbackPlus T A)
    (Etale.upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus
    (upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus
    (closureSquareEtaleFactor A c v) (closureSquareEtaleClosure A s.toImage s.imageι)
    (closureSquareProEtaleFactor A c v) (closureSquareProEtaleClosure A s.toImage s.imageι)
    (fixedComparisonPullbackPlus A s) (closureSquareDelta A c v)
    (closureSquareB A s.toImage s.imageι) qe qp
    (closureSquareEtaleFactorRestriction A s c v h)
    (closureSquareEtaleClosureRestriction A s s.toImage s.imageι s.toImage_imageι)
    (closureSquareProEtaleFactorRestriction A s c v h)
    (closureSquareProEtaleClosureRestriction A s s.toImage s.imageι s.toImage_imageι)
    he hp hF hE
  · intro L
    have : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion v
    have : TopologicalSpace.NoetherianSpace V :=
      v.isOpenEmbedding.isInducing.noetherianSpace
    have := (derivedImmersionClosed_normalization A c L).2.2.2
    dsimp only [closureSquareProEtaleFactorRestriction, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  · intro L f g hh
    apply closure_factor_injective A c v
      ((siteComparisonDerivedPullbackPlus S A).obj L)
    have hn := (closureSquareProEtalePullComp A c v s h).hom.naturality f
    have hn' := (closureSquareProEtalePullComp A c v s h).hom.naturality g
    dsimp only [Functor.comp_map] at hn hn'
    apply (cancel_epi ((closureSquareProEtalePullComp A c v s h).hom.app _)).1
    rw [← hn, ← hn', hh]


/-- The normalized change-of-factorization square, and identity restriction on both sites.

Proof: apply the closure square to each factorization, then cancel the primed
pro-etale closure identification. For the two restriction identities, substitute the
normalization of the primed identification and cancel its inverse with its forward
map. The unprimed normalization gives the result.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
theorem locallyClosed_closure_comparison_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V V' T : Scheme.{u}} [IsNoetherian T] (s : S ⟶ T) [IsImmersion s]
    (c : S ⟶ V) (v : V ⟶ T) (c' : S ⟶ V') (v' : V' ⟶ T)
    [IsClosedImmersion c] [IsOpenImmersion v]
    [IsClosedImmersion c'] [IsOpenImmersion v'] (h : c ≫ v = s) (h' : c' ≫ v' = s)
    (qe : closureSquareEtaleFactor A c v ≅ closureSquareEtaleClosure A s.toImage s.imageι)
    (qp : closureSquareProEtaleFactor A c v ≅
      closureSquareProEtaleClosure A s.toImage s.imageι)
    (qe' : closureSquareEtaleFactor A c' v' ≅ closureSquareEtaleClosure A s.toImage s.imageι)
    (qp' : closureSquareProEtaleFactor A c' v' ≅
      closureSquareProEtaleClosure A s.toImage s.imageι)
    (he : closureSquareEtaleNormalized A s c v h qe)
    (hp : closureSquareProEtaleNormalized A s c v h qp)
    (he' : closureSquareEtaleNormalized A s c' v' h' qe')
    (hp' : closureSquareProEtaleNormalized A s c' v' h' qp') :
    ((closureSquareDelta A c v).hom ≫
        Functor.whiskerLeft (siteComparisonDerivedPullbackPlus S A)
          (closureSquareChange qp qp').hom =
      Functor.whiskerRight (closureSquareChange qe qe').hom
          (siteComparisonDerivedPullbackPlus T A) ≫
        (closureSquareDelta A c' v').hom) ∧
    (Functor.whiskerRight (closureSquareChange qe qe').hom
          (Etale.upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ≫
        closureSquareEtaleFactorRestriction A s c' v' h' =
      closureSquareEtaleFactorRestriction A s c v h) ∧
    (Functor.whiskerRight (closureSquareChange qp qp').hom
          (upperStar (ModuleCat.{u + 1} A) s).mapDerivedCategoryPlus ≫
        closureSquareProEtaleFactorRestriction A s c' v' h' =
      closureSquareProEtaleFactorRestriction A s c v h) := by
  have h₁ := (locallyClosed_closure_comparison_square A s c v h qe qp he hp).1
  have h₂ := (locallyClosed_closure_comparison_square A s c' v' h' qe' qp' he' hp').1
  refine ⟨?_, ?_, ?_⟩
  · apply NatTrans.ext
    funext L
    apply (cancel_mono
      (qp'.hom.app ((siteComparisonDerivedPullbackPlus S A).obj L))).1
    have h₁L := congr_app h₁ L
    have h₂L := congr_app h₂ L
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h₁L h₂L
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      closureSquareChange, Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
    rw [Iso.inv_hom_id_app, Category.comp_id, h₁L, h₂L]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  · dsimp only [closureSquareEtaleNormalized] at he he'
    apply NatTrans.ext
    funext L
    have hL := congr_app he L
    have hL' := congr_app he' L
    simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hL hL'
    simp only [closureSquareChange, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
    rw [← hL']
    simpa only [← Functor.map_comp_assoc, Category.assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using hL
  · dsimp only [closureSquareProEtaleNormalized] at hp hp'
    apply NatTrans.ext
    funext L
    have hL := congr_app hp L
    have hL' := congr_app hp' L
    simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hL hL'
    simp only [closureSquareChange, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
    rw [← hL']
    simpa only [← Functor.map_comp_assoc, Category.assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using hL

/-- The identity and cocycle laws for Etale change maps through the common closure.

Proof: step 6 of the node. Expand t as q followed by inverse q'. Adjacent q' and
its inverse cancel. For the identity, q followed by its inverse is the identity.
The same cancellation holds before descent, hence the laws are termwise as well.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
theorem locallyClosed_closure_comparison_etale_laws
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V₁ V₂ V₃ T : Scheme.{u}} [IsNoetherian T] (s : S ⟶ T) [IsImmersion s]
    (c₁ : S ⟶ V₁) (v₁ : V₁ ⟶ T) (c₂ : S ⟶ V₂) (v₂ : V₂ ⟶ T)
    (c₃ : S ⟶ V₃) (v₃ : V₃ ⟶ T)
    [IsClosedImmersion c₁] [IsOpenImmersion v₁]
    [IsClosedImmersion c₂] [IsOpenImmersion v₂]
    [IsClosedImmersion c₃] [IsOpenImmersion v₃]
    (q₁ : closureSquareEtaleFactor A c₁ v₁ ≅
      closureSquareEtaleClosure A s.toImage s.imageι)
    (q₂ : closureSquareEtaleFactor A c₂ v₂ ≅
      closureSquareEtaleClosure A s.toImage s.imageι)
    (q₃ : closureSquareEtaleFactor A c₃ v₃ ≅
      closureSquareEtaleClosure A s.toImage s.imageι) :
    closureSquareChange q₁ q₁ = Iso.refl _ ∧
      closureSquareChange q₁ q₂ ≪≫ closureSquareChange q₂ q₃ =
        closureSquareChange q₁ q₃ := by
  constructor
  · simp [closureSquareChange]
  · simp [closureSquareChange, Iso.trans_assoc]

/-- The identity and cocycle laws for ProEtale change maps through the common closure.

Proof: step 6 of the node. Expand t as q followed by inverse q'. Adjacent q' and
its inverse cancel. For the identity, q followed by its inverse is the identity.
The same cancellation holds before descent, hence the laws are termwise as well.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 0B65
(blueprint: lem-sf-locally-closed-closure-comparison-square). -/
theorem locallyClosed_closure_comparison_proetale_laws
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V₁ V₂ V₃ T : Scheme.{u}} [IsNoetherian T] (s : S ⟶ T) [IsImmersion s]
    (c₁ : S ⟶ V₁) (v₁ : V₁ ⟶ T) (c₂ : S ⟶ V₂) (v₂ : V₂ ⟶ T)
    (c₃ : S ⟶ V₃) (v₃ : V₃ ⟶ T)
    [IsClosedImmersion c₁] [IsOpenImmersion v₁]
    [IsClosedImmersion c₂] [IsOpenImmersion v₂]
    [IsClosedImmersion c₃] [IsOpenImmersion v₃]
    (q₁ : closureSquareProEtaleFactor A c₁ v₁ ≅
      closureSquareProEtaleClosure A s.toImage s.imageι)
    (q₂ : closureSquareProEtaleFactor A c₂ v₂ ≅
      closureSquareProEtaleClosure A s.toImage s.imageι)
    (q₃ : closureSquareProEtaleFactor A c₃ v₃ ≅
      closureSquareProEtaleClosure A s.toImage s.imageι) :
    closureSquareChange q₁ q₁ = Iso.refl _ ∧
      closureSquareChange q₁ q₂ ≪≫ closureSquareChange q₂ q₃ =
        closureSquareChange q₁ q₃ := by
  constructor
  · simp [closureSquareChange]
  · simp [closureSquareChange, Iso.trans_assoc]

/-- Identity and cocycle laws before termwise descent, on both module-sheaf sites.
Source: blueprint locally closed comparison, second paragraph; Stacks 0GJ1 and 04CA
(blueprint: lem-sf-locally-closed-closure-comparison-square).

Proof: step 6 of the node. On each site t_ab is q_a followed by inverse q_b.
Cancel q_b with its inverse for the cocycle and q_a with its inverse for identity.
No point, support or coefficient nonvanishing assumption occurs. -/
theorem locallyClosed_closure_comparison_termwise_laws
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V₁ V₂ V₃ T : Scheme.{u}} [IsNoetherian T] (s : S ⟶ T) [IsImmersion s]
    (c₁ : S ⟶ V₁) (v₁ : V₁ ⟶ T) (c₂ : S ⟶ V₂) (v₂ : V₂ ⟶ T)
    (c₃ : S ⟶ V₃) (v₃ : V₃ ⟶ T)
    [IsClosedImmersion c₁] [IsOpenImmersion v₁]
    [IsClosedImmersion c₂] [IsOpenImmersion v₂]
    [IsClosedImmersion c₃] [IsOpenImmersion v₃]
    (qe1 : Etale.lowerStar (ModuleCat.{u + 1} A) c₁ ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v₁ ≅
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage ⋙
        Etale.lowerStar (ModuleCat.{u + 1} A) s.imageι)
    (qe2 : Etale.lowerStar (ModuleCat.{u + 1} A) c₂ ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v₂ ≅
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage ⋙
        Etale.lowerStar (ModuleCat.{u + 1} A) s.imageι)
    (qe3 : Etale.lowerStar (ModuleCat.{u + 1} A) c₃ ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) v₃ ≅
      Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage ⋙
        Etale.lowerStar (ModuleCat.{u + 1} A) s.imageι)
    (qp1 : lowerStar (ModuleCat.{u + 1} A) c₁ ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) v₁ ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage ⋙
        lowerStar (ModuleCat.{u + 1} A) s.imageι)
    (qp2 : lowerStar (ModuleCat.{u + 1} A) c₂ ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) v₂ ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage ⋙
        lowerStar (ModuleCat.{u + 1} A) s.imageι)
    (qp3 : lowerStar (ModuleCat.{u + 1} A) c₃ ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) v₃ ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) s.toImage ⋙
        lowerStar (ModuleCat.{u + 1} A) s.imageι) :
    (closureSquareChange qe1 qe1 = Iso.refl _) ∧
    (closureSquareChange qe1 qe2 ≪≫ closureSquareChange qe2 qe3 =
      closureSquareChange qe1 qe3) ∧
    (closureSquareChange qp1 qp1 = Iso.refl _) ∧
    (closureSquareChange qp1 qp2 ≪≫ closureSquareChange qp2 qp3 =
      closureSquareChange qp1 qp3) := by
  simp [closureSquareChange, Iso.trans_assoc]

end AlgebraicGeometry.ProEtale
