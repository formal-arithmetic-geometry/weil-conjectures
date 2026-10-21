/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison
public import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

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

universe u uC uD vC vD

open CategoryTheory CategoryTheory.Limits

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

/-- The specified closure square, together with both restriction-normalization equations.
Source: blueprint main-20261015, locally closed comparison sentence; Stacks 09AF, 099R,
0B65, 0GJ1 and 04CA
(blueprint: lem-sf-locally-closed-closure-comparison-square).

Proof plan (the six steps of the node):
1. The open intermediate scheme, the source and the closure are Noetherian, by open
   inheritance and finite-type inheritance. The etale extension comparison and pro-etale
   locally closed extension coherence give the identity-normalized closure maps. Closed
   direct images are exact and their specified derived mates are the termwise ones by
   lem-sf-derived-immersion-comparison-normalization. Exact-functor boundedness makes all
   mate inputs admissible. The open comparison and closed mate are isomorphisms, so Delta
   and B are their whiskered isomorphisms.
2. Factor restriction uses the inverse open unit and closed counit; closure restriction
   uses the closed counit and inverse open unit. Both start with the pullback compositor
   for the same s. Normalization of q is exactly the displayed restriction equation.
3. The open unit equation followed by the closed counit equation removes the two
   comparisons in Delta after restriction. Pullback-comparison composition identifies the
   resulting successive comparisons with fixedComparisonPullbackPlus A s.
4. For B, naturality moves the closed counit across the image of the open comparison;
   the closed normalization and then the open unit equation remove both comparisons.
   The same compositor for s gives the second restriction equation.
5. Restrict the two sides of the closure square. Steps 2--4 and pullback-comparison
   naturality make them equal. Conjugate by inverse Delta and inverse q_p to endomorphisms
   of the factorized extension. The restriction Hom bijection of
   lem-sfb-locally-closed-extension-coherence detects equality; cancel the conjugations.
6. Apply the same square to a second factorization and cancel its q'_p. This gives the
   change square. The quotients of normalized q maps are normalized; inverse cancellation
   gives the identity and cocycle laws, also termwise. Empty S, open or closed s and A=0
   use the same units, counits and inverse cancellations. -/
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
  sorry

/-- The normalized change-of-factorization square, and identity restriction on both sites.

Proof plan (the six steps of the node):
1. The open intermediate scheme, the source and the closure are Noetherian, by open
   inheritance and finite-type inheritance. The etale extension comparison and pro-etale
   locally closed extension coherence give the identity-normalized closure maps. Closed
   direct images are exact and their specified derived mates are the termwise ones by
   lem-sf-derived-immersion-comparison-normalization. Exact-functor boundedness makes all
   mate inputs admissible. The open comparison and closed mate are isomorphisms, so Delta
   and B are their whiskered isomorphisms.
2. Factor restriction uses the inverse open unit and closed counit; closure restriction
   uses the closed counit and inverse open unit. Both start with the pullback compositor
   for the same s. Normalization of q is exactly the displayed restriction equation.
3. The open unit equation followed by the closed counit equation removes the two
   comparisons in Delta after restriction. Pullback-comparison composition identifies the
   resulting successive comparisons with fixedComparisonPullbackPlus A s.
4. For B, naturality moves the closed counit across the image of the open comparison;
   the closed normalization and then the open unit equation remove both comparisons.
   The same compositor for s gives the second restriction equation.
5. Restrict the two sides of the closure square. Steps 2--4 and pullback-comparison
   naturality make them equal. Conjugate by inverse Delta and inverse q_p to endomorphisms
   of the factorized extension. The restriction Hom bijection of
   lem-sfb-locally-closed-extension-coherence detects equality; cancel the conjugations.
6. Apply the same square to a second factorization and cancel its q'_p. This gives the
   change square. The quotients of normalized q maps are normalized; inverse cancellation
   gives the identity and cocycle laws, also termwise. Empty S, open or closed s and A=0
   use the same units, counits and inverse cancellations.
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
  sorry

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
  sorry

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
  sorry

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
  sorry

end AlgebraicGeometry.ProEtale
