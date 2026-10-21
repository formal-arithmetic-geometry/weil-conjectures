/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCoordinateSupport
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.SupportedCupFunctoriality
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.AlgebraicGeometry.PointedEtaleStalk
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.EtaleInjectiveSupportSequence
import Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple
import Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Affine continuity of coordinate supported stalks

Source: Stacks Project, Tags 0EYM, 09XP and 0A45, and the coordinate-model
refinement argument (blueprint: lem-pur-affine-coordinate-support-stalk-continuity).

The legs below derive the unique factorization through the actual support kernel.
A colimit assertion includes its cocone, so it specifies the comparison map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Arbitrary inverse-image supported germs, normalized by the kernel inclusion.
Source: Stacks 09XP, kernel support, and 0EYM, canonical exchange
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: inverse image is exact. The pulled-back support kernel restricts to zero on
 the inverse-image complement. The ordinary stalk pullback therefore factors uniquely
 through the target support kernel. Exactness of the geometric stalk preserves that
 kernel; cancel its monic inclusion for uniqueness. This is the same construction
 as coordinateStalkRestriction, without the unnecessary etaleness restriction. -/
theorem affineSupportGerm_existsUnique (A : Type (u + 1)) [CommRing A]
    {Z X Z' T : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ T) [IsClosedImmersion i'] (f : T ⟶ X)
    (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    ∃! m : coordinateSupportedStalk A i (t ≫ f) ⟶
        upperStar (ModuleCat.{u + 1} A) f ⋙ coordinateSupportedStalk A i' t,
      m ≫ Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) f)
          (coordinateSupportedStalkInclusion A i' t) =
        coordinateSupportedStalkInclusion A i (t ≫ f) ≫
          (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f t).inv := by
  sorry

/-- The unique supported germ leg for an arbitrary map of pairs.
Source: Stacks 09XP and 0EYM
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def affineSupportGerm (A : Type (u + 1)) [CommRing A]
    {Z X Z' T : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ T) [IsClosedImmersion i'] (f : T ⟶ X)
    (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    coordinateSupportedStalk A i (t ≫ f) ⟶
      upperStar (ModuleCat.{u + 1} A) f ⋙ coordinateSupportedStalk A i' t :=
  (affineSupportGerm_existsUnique A i i' f hf t).choose

/-- Derive that specific germ factorization, using exact inverse image.
Source: Stacks 0EYM and 09XP
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def affineDerivedSupportGerm (A : Type (u + 1)) [CommRing A]
    {Z X Z' T : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ T) [IsClosedImmersion i'] (f : T ⟶ X)
    (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    (coordinateSupportedStalk A i (t ≫ f)).rightDerivedFunctorPlus ⟶
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus ⋙
        (coordinateSupportedStalk A i' t).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := coordinateSupportedStalk A i (t ≫ f))
      (G' := coordinateSupportedStalk A i' t)
      (β := upperStar (ModuleCat.{u + 1} A) f) (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ affineSupportGerm A i i' f hf t)

end AlgebraicGeometry.Etale

namespace WeilConjectures.PurityFiniteSetting

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- The coordinate space, with the universe-lifted finite coordinate set.
Source: Stacks 0EYM, coordinate model
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
abbrev continuitySpace (R : Type u) [CommRing R] (b : ℕ) : AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.AffineSpace (ULift.{u} (Fin b))
    (AlgebraicGeometry.Spec (CommRingCat.of R))

/-- Its actual zero section; its open complement defines the support functor.
Source: Stacks 09XP, coordinate model
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
abbrev continuityOrigin (R : Type u) [CommRing R] (b : ℕ) :=
  AlgebraicGeometry.AffineSpace.zeroSection (ULift.{u} (Fin b))
    (AlgebraicGeometry.Spec (CommRingCat.of R))

/-- Affine coordinate base change, including transitions and limit projections.
Source: Stacks 0EYM
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (b : ℕ) :
    continuitySpace S b ⟶ continuitySpace R b :=
  AlgebraicGeometry.AffineSpace.map (ULift.{u} (Fin b))
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f))

/-- Base change of the coordinate zero locus, also for no coordinates.
Source: the common coordinate zero locus, Stacks 0EYM
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: the image of the zero section is the common vanishing locus of the coordinates.
The affine-space base-change map pulls each coordinate back to the same coordinate.
Taking inverse images of their common vanishing loci gives the equality. For b=0
both loci are the entire space. -/
theorem continuityMap_support {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (b : ℕ) :
    Set.range (continuityOrigin S b).base =
      (continuityMap f b).base ⁻¹' Set.range (continuityOrigin R b).base := by
  sorry

/-- Cohomology of the derived supported stalk, naturally in the coefficient sheaf.
By coordinateSupportedStalkDerivationIso and exactness of stalks this is the stalk
of H^d(RQ(F)). Source: Stacks 09XP and 0A45
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityH (R : Type u) [CommRing R] (b : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : AlgebraicGeometry.Spec (.of Ω) ⟶ continuitySpace R b) (d : ℤ) :
    Sheaf (continuitySpace R b).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) ⥤
      ModuleCat.{u + 1} P.Coefficient :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (AlgebraicGeometry.Etale.coordinateSupportedStalk P.Coefficient
      (continuityOrigin R b) x).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor _ d

/-- The finite signed Tate sheaf, at an annihilator valid for every positive level.
Source: Stacks 03PK; the finite twists of the purity conventions
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
abbrev continuityTwist (R : Type u) [CommRing R] (b : ℕ) (r : ℤ) :=
  P.functorialCupTwist false (continuitySpace R b) r

/-- The supported cohomology module in the displayed continuity assertion.
Source: Stacks 09XP and 0EYM
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
abbrev continuityStalk (R : Type u) [CommRing R] (b : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : AlgebraicGeometry.Spec (.of Ω) ⟶ continuitySpace R b) (r d : ℤ) :=
  (P.continuityH R b x d).obj (P.continuityTwist R b r)

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- Canonical supported pullback on cohomology, with a specified coefficient map.
Source: Stacks 0EYM and 09XP
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityLeg {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (b : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace S b) (d : ℤ)
    (F : Sheaf (continuitySpace R b).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (G : Sheaf (continuitySpace S b).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (c : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (continuityMap f b)).obj F ⟶ G) :
    (P.continuityH R b (x ≫ continuityMap f b) d).obj F ⟶
      (P.continuityH S b x d).obj G :=
  (DerivedCategory.Plus.homologyFunctor _ d).map
    ((Etale.affineDerivedSupportGerm P.Coefficient (continuityOrigin R b)
      (continuityOrigin S b) (continuityMap f b) (continuityMap_support f b) x).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (Etale.coordinateSupportedStalk P.Coefficient
        (continuityOrigin S b) x).rightDerivedFunctorPlus.map
          (((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
            (continuityMap f b)).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
            (DerivedCategory.Plus.singleFunctor _ 0).map c))

/-- The structure map of a coordinate space over the ground field.
Source: coordinate models of Stacks 0EYM
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityStructure (R : Type u) [CommRing R] [Algebra P.field.k R] (b : ℕ) :
    continuitySpace R b ⟶ Spec (.of P.field.k) :=
  (continuitySpace R b ↘ Spec (.of R)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap P.field.k R))

/-- Pullback of an arbitrary ground coefficient line or its tensor/dual expression.
This functor lets all compatibility assertions use the actual coefficient maps.
Source: Stacks 03PK, constant finite lines over the algebraically closed ground field
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityCoefficient (R : Type u) [CommRing R] [Algebra P.field.k R] (b : ℕ) :=
  Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (P.continuityStructure R b)

/-- A coordinate base-change map is a map over the ground field.
Source: the affine-space projection, Stacks 0EYM
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: the affine-space map commutes with its first projection. On affine bases,
Spec reverses composition and the algebra-map equation is f.commutes. -/
theorem continuityStructure_map {R S : Type u} [CommRing R] [CommRing S]
    [Algebra P.field.k R] [Algebra P.field.k S] (f : R →ₐ[P.field.k] S) (b : ℕ) :
    continuityMap f.toRingHom b ≫ P.continuityStructure R b =
      P.continuityStructure S b := by
  sorry

/-- The actual inverse-image composition comparison for coefficient lines.
Source: Stacks 03Q1 and 0EYM
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityCoefficientPullback {R S : Type u} [CommRing R] [CommRing S]
    [Algebra P.field.k R] [Algebra P.field.k S] (f : R →ₐ[P.field.k] S) (b : ℕ) :
    P.continuityCoefficient R b ⋙
        Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (continuityMap f.toRingHom b) ≅
      P.continuityCoefficient S b :=
  (Etale.upperStarComp (ModuleCat.{u + 1} P.Coefficient)
    (continuityMap f.toRingHom b) (P.continuityStructure R b)
    (P.continuityStructure S b) (P.continuityStructure_map f b).symm).symm

/-- Cohomology of a pulled-back ground coefficient, naturally in that coefficient.
Source: Stacks 09XP and 03PK
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityGroundH (R : Type u) [CommRing R] [Algebra P.field.k R] (b : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b) (d : ℤ) :=
  P.continuityCoefficient R b ⋙ P.continuityH R b x d

/-- The normalized leg for a ground coefficient and a map of affine bases.
Source: Stacks 0EYM and 09XP
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityGroundLeg {R S : Type u} [CommRing R] [CommRing S]
    [Algebra P.field.k R] [Algebra P.field.k S] (f : R →ₐ[P.field.k] S) (b : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace S b) (d : ℤ)
    (F : Sheaf (Spec (.of P.field.k)).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    (P.continuityGroundH R b (x ≫ continuityMap f.toRingHom b) d).obj F ⟶
      (P.continuityGroundH S b x d).obj F :=
  P.continuityLeg f.toRingHom b x d ((P.continuityCoefficient R b).obj F)
    ((P.continuityCoefficient S b).obj F) ((P.continuityCoefficientPullback f b).hom.app F)

/-- Index of all finitely generated subalgebras, ordered by inclusion. The existing
fgSubalgebraDiagramOf supplies its ring maps. Source: Stacks 0EYM, affine reduction
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
abbrev ContinuityIndex (R : Type u) [CommRing R] [Algebra P.field.k R] :=
  {S : Subalgebra P.field.k R // S.FG}

/-- The limit projection belonging to a finitely generated subalgebra.
Source: Stacks 0EYM
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityProjection (R : Type u) [CommRing R] [Algebra P.field.k R]
    (b : ℕ) (i : P.ContinuityIndex R) : continuitySpace R b ⟶ continuitySpace i.1 b :=
  continuityMap i.1.val.toRingHom b

/-- The stage point is the image of the fixed geometric point.
Source: Stacks 03Q1 and 0EYM
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityPoint (R : Type u) [CommRing R] [Algebra P.field.k R] (b : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b) (i : P.ContinuityIndex R) :=
  x ≫ P.continuityProjection R b i

/-- The stage stalk of the pulled-back coefficient.
Source: Stacks 0EYM and 09XP
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityStage (R : Type u) [CommRing R] [Algebra P.field.k R] (b : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b) (d : ℤ) (i : P.ContinuityIndex R) :=
  P.continuityGroundH i.1 b (P.continuityPoint R b x i) d

/-- Compatibility of image points for inclusion of subalgebras.
Source: Stacks 0EYM, projection identities
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: Spec reverses composition of the inclusion ring maps and AffineSpace.map
preserves composition. Associate the composite with x and cancel the inclusions. -/
theorem continuityPoint_transition (R : Type u) [CommRing R] [Algebra P.field.k R]
    (b : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b) {i j : P.ContinuityIndex R} (a : i ⟶ j) :
    P.continuityPoint R b x j ≫
        continuityMap (Subalgebra.inclusion (show i.1 ≤ j.1 from leOfHom a)).toRingHom b =
      P.continuityPoint R b x i := by
  sorry

/-- The specified supported transition, with the image-point identity transported.
Source: Stacks 0EYM, maps defined from the support localization units
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityTransition (R : Type u) [CommRing R] [Algebra P.field.k R]
    (b : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b) (d : ℤ)
    (F : Sheaf (Spec (.of P.field.k)).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    {i j : P.ContinuityIndex R} (a : i ⟶ j) :
    (P.continuityStage R b x d i).obj F ⟶ (P.continuityStage R b x d j).obj F :=
  eqToHom (congrArg
    (fun y ↦ (P.continuityGroundH i.1 b y d).obj F)
    (P.continuityPoint_transition R b x a).symm) ≫
  P.continuityGroundLeg (Subalgebra.inclusion (show i.1 ≤ j.1 from leOfHom a)) b
    (P.continuityPoint R b x j) d F

/-- The canonical supported limit leg.
Source: Stacks 0EYM, comparison on representatives
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityLimitLeg (R : Type u) [CommRing R] [Algebra P.field.k R]
    (b : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b) (d : ℤ)
    (F : Sheaf (Spec (.of P.field.k)).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (i : P.ContinuityIndex R) :
    (P.continuityStage R b x d i).obj F ⟶ (P.continuityGroundH R b x d).obj F :=
  P.continuityGroundLeg i.1.val b x d F

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry
variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- The supported transitions satisfy the functor laws, and the limit legs form a
cocone. Source: Stacks 0EYM, compatibility of exchanges, and 09XP, kernel uniqueness
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: the underived comparisons are uniquely fixed by their kernel inclusions.
Identity and composition follow by cancelling those inclusions and using ordinary
pullback-stalk coherence. Derivation preserves these equations by the unit
normalization of rightDerivedFunctorPlusBaseChange. Coefficient pullback composition
is the inverse-image associativity isomorphism. Taking degree d preserves composition.
The same argument with a limit projection gives the cocone equation. -/
theorem continuity_transition_laws (R : Type u) [CommRing R] [Algebra P.field.k R]
    (b : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b) (d : ℤ)
    (F : Sheaf (Spec (.of P.field.k)).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    (∀ i : P.ContinuityIndex R, P.continuityTransition R b x d F (𝟙 i) = 𝟙 _) ∧
    (∀ (i j k : P.ContinuityIndex R) (a : i ⟶ j) (c : j ⟶ k),
      P.continuityTransition R b x d F (a ≫ c) =
        P.continuityTransition R b x d F a ≫ P.continuityTransition R b x d F c) ∧
    (∀ (i j : P.ContinuityIndex R) (a : i ⟶ j),
      P.continuityTransition R b x d F a ≫ P.continuityLimitLeg R b x d F j =
        P.continuityLimitLeg R b x d F i) := by
  sorry

/-- The actual diagram of coordinate supported stalks.
Source: Stacks 0EYM, specified supported transitions
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityDiagram (R : Type u) [CommRing R] [Algebra P.field.k R]
    (b : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b) (d : ℤ)
    (F : Sheaf (Spec (.of P.field.k)).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    P.ContinuityIndex R ⥤ ModuleCat.{u + 1} P.Coefficient where
  obj i := (P.continuityStage R b x d i).obj F
  map a := P.continuityTransition R b x d F a
  map_id i := (P.continuity_transition_laws R b x d F).1 i
  map_comp a c := (P.continuity_transition_laws R b x d F).2.1 _ _ _ a c

/-- The cocone whose legs are the normalized supported pullbacks.
Source: Stacks 0EYM
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityCocone (R : Type u) [CommRing R] [Algebra P.field.k R]
    (b : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b) (d : ℤ)
    (F : Sheaf (Spec (.of P.field.k)).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    Cocone (P.continuityDiagram R b x d F) where
  pt := (P.continuityGroundH R b x d).obj F
  ι := { app i := P.continuityLimitLeg R b x d F i
         naturality i j a := by
           exact ((P.continuity_transition_laws R b x d F).2.2 i j a).trans
             (Category.comp_id _).symm }

/-- The canonical A-linear colimit comparison, without choosing an isomorphism.
Source: Stacks 0EYM and 09XP
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityComparison (R : Type u) [CommRing R] [Algebra P.field.k R]
    (b : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b) (d : ℤ)
    (F : Sheaf (Spec (.of P.field.k)).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    colimit (P.continuityDiagram R b x d F) ⟶ (P.continuityGroundH R b x d).obj F :=
  colimit.desc _ (P.continuityCocone R b x d F)

/-- Affine continuity for the finite signed Tate line, in every integer degree.
Source: Stacks 0EYM, 09XP and 0A45, with the nine-step coordinate argument
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof:
1. The punctured b-space is the finite union of D(t_h). Its open immersion is qcqs;
all transition maps are affine. The punctured spaces are base changes of the model
at k, so their limit is the punctured limit space, also after cofinal reindexing.
2. The finite root polynomial splits over algebraically closed k, with pairwise
comaximal linear factors. Thus each signed finite twist is the pulled-back constant
line L_r, including negative twists by duality, with identity coefficient transitions.
3. Enough injectives and bounded-below injective resolutions compute RQ. Apply
lem-pur-etale-injective-support-sequence and the bounded-below derived-functor unit.
The localization sequence identifies degrees zero and one as the kernel and cokernel
of F to j_*F|U; higher degrees are the shifted higher direct images of j. All negative
degrees vanish.
4. On resolutions, exact inverse image and K-injective comparison give the maps of
support sequences. Their kernel maps are exactly affineSupportGerm; homotopy
uniqueness gives composition and the connecting-map squares.
5. Apply lem-kun-0eym to the punctured opens. The cartesian coefficient-forgetting
exchange theorem identifies the actual module maps, and exact stalks give the
higher-image stalk comparisons. The central coefficient comparison is identity on L_r.
6. Exact filtered colimits preserve the kernel and cokernel sequence, proving degrees
zero and one. The shifted higher-image comparisons give all higher degrees.
7. Every construction is natural in coefficient maps, tensor identifications and
evaluation. Ordered coordinate Kummer products and their boundaries pull back by
lem-pur-supported-cup-functoriality. The kernel-normalized global-to-stalk map sends
their supported germs to the same germs at every stage and at the limit.
8. A cofinal family represents every class and equality. Stages containing f yield
the localization system R_i[1/f], whose union is R[1/f]. The canonical comparison
squares commute by step 4. Principal affine refinements prove the common-affine
agreement for two neighbourhoods with base-change-compatible finite orientations.
9. For b=0, the complements are empty and Q is the identity: degree zero is L_r and
all other degrees vanish. For R=0 there is no geometric point to check. -/
theorem affine_coordinate_support_stalk_continuity
    (R : Type u) [CommRing R] [Algebra P.field.k R] (b : ℕ) (r d : ℤ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b)
    (hx : Set.range x.base ⊆ Set.range (continuityOrigin R b).base) :
    IsIso (P.continuityComparison R b x d
      (P.functorialCupTwist false (Spec (.of P.field.k)) r)) ∧
    (d < 0 →
      IsZero (colimit (P.continuityDiagram R b x d
        (P.functorialCupTwist false (Spec (.of P.field.k)) r))) ∧
      IsZero ((P.continuityGroundH R b x d).obj
        (P.functorialCupTwist false (Spec (.of P.field.k)) r))) := by
  sorry

/-- The comparison is independent of any cofinal directed reindexing, via the
canonical reindexing map. This includes all cofinal families of finitely generated
subalgebras with union R. Source: Stacks 0EYM and filtered-colimit representatives
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: every class and every equality has a representative at one stage. Cofinality
moves it to the chosen family, proving both surjectivity and injectivity. Both
composites on a representative are the same limit leg, so the comparison equality
follows from the colimit universal property. -/
theorem continuity_cofinal (R : Type u) [CommRing R] [Algebra P.field.k R]
    (b : ℕ) (r d : ℤ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b)
    (hx : Set.range x.base ⊆ Set.range (continuityOrigin R b).base)
    {J : Type u} [PartialOrder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (e : J ⥤ P.ContinuityIndex R) [e.Final] :
    IsIso (colimit.pre (P.continuityDiagram R b x d
      (P.functorialCupTwist false (Spec (.of P.field.k)) r)) e) ∧
    IsIso (colimit.desc _ ((P.continuityCocone R b x d
      (P.functorialCupTwist false (Spec (.of P.field.k)) r)).whisker e)) ∧
    colimit.pre (P.continuityDiagram R b x d
        (P.functorialCupTwist false (Spec (.of P.field.k)) r)) e ≫
      P.continuityComparison R b x d
        (P.functorialCupTwist false (Spec (.of P.field.k)) r) =
      colimit.desc _ ((P.continuityCocone R b x d
        (P.functorialCupTwist false (Spec (.of P.field.k)) r)).whisker e) := by
  sorry

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry
variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- The canonical identification of the coefficient used above with the literal
finite Tate sheaf on the coordinate space. Source: Stacks 03PK and 03Q1
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityTwistIdentification (R : Type u) [CommRing R] [Algebra P.field.k R]
    (b : ℕ) (r : ℤ) :
    (P.continuityCoefficient R b).obj
        (P.functorialCupTwist false (Spec (.of P.field.k)) r) ≅ P.continuityTwist R b r :=
  P.functorialCupEtaleTwistPullback (P.continuityStructure R b) (𝟙 _) r

/-- Every coefficient map commutes with the normalized supported legs. In particular
this applies to maps of L_r, their signed tensor identifications and dual evaluation.
Source: Stacks 09XP and 0EYM, naturality of all kernel and derived units
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: affineSupportGerm is a natural transformation; so is its canonical derived
base change. Compose its naturality with the naturality of inverse-image composition
and the degree-zero embedding, then apply H^d. Tensor and dual identifications are
particular maps in this same coefficient category, with the normalized Tate pullbacks. -/
theorem continuity_coefficient_naturality {R S : Type u} [CommRing R] [CommRing S]
    [Algebra P.field.k R] [Algebra P.field.k S] (f : R →ₐ[P.field.k] S) (b : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace S b) (d : ℤ)
    {F G : Sheaf (Spec (.of P.field.k)).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)} (a : F ⟶ G) :
    (P.continuityGroundH R b (x ≫ continuityMap f.toRingHom b) d).map a ≫
        P.continuityGroundLeg f b x d G =
      P.continuityGroundLeg f b x d F ≫ (P.continuityGroundH S b x d).map a := by
  sorry

/-- Naturality of the transitions after the canonical image-point transport.
Source: Stacks 0EYM and 09XP
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: apply continuity_coefficient_naturality to the inclusion of subalgebras.
Move the image-point equality through the coefficient morphism by eqToHom_naturality. -/
theorem continuity_transition_coefficient (R : Type u) [CommRing R]
    [Algebra P.field.k R] (b : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b) (d : ℤ)
    {F G : Sheaf (Spec (.of P.field.k)).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)} (a : F ⟶ G)
    {i j : P.ContinuityIndex R} (h : i ⟶ j) :
    P.continuityTransition R b x d F h ≫ (P.continuityStage R b x d j).map a =
      (P.continuityStage R b x d i).map a ≫ P.continuityTransition R b x d G h := by
  sorry

/-- Coefficient maps on the diagram, defined componentwise, not chosen after taking
colimits. Source: Stacks 0EYM, coefficient naturality
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityCoefficientMap (R : Type u) [CommRing R] [Algebra P.field.k R]
    (b : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b) (d : ℤ)
    {F G : Sheaf (Spec (.of P.field.k)).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)} (a : F ⟶ G) :
    P.continuityDiagram R b x d F ⟶ P.continuityDiagram R b x d G where
  app i := (P.continuityStage R b x d i).map a
  naturality _i _j h := P.continuity_transition_coefficient R b x d a h

/-- Naturality of the colimit comparison for all coefficient maps, hence for the
specified constant-line tensor and dual identifications.
Source: Stacks 0EYM and 09XP
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: precompose the equality with each colimit injection. The canonical colimit
map sends that injection to the corresponding component. The two paths agree by
continuity_coefficient_naturality; the colimit universal property finishes. -/
theorem continuity_comparison_coefficient (R : Type u) [CommRing R]
    [Algebra P.field.k R] (b : ℕ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b) (d : ℤ)
    {F G : Sheaf (Spec (.of P.field.k)).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)} (a : F ⟶ G) :
    colim.map (P.continuityCoefficientMap R b x d a) ≫
        P.continuityComparison R b x d G =
      P.continuityComparison R b x d F ≫ (P.continuityGroundH R b x d).map a := by
  sorry

/-- The affine supported legs compose, for arbitrary ground coefficient maps.
In particular these are the commuting ladders for R_i to R_i[1/f] and R to R[1/f].
Source: Stacks 0EYM and 09XP
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: both composites have the same underived kernel-inclusion equation. Uniqueness
identifies them, and uniqueness of derived comparison preserves this identity.
The inverse-image composition isomorphisms obey the associativity identity. Apply
H^d; the displayed equality of points accounts for the sole equality transport. -/
theorem continuity_leg_composition {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra P.field.k R] [Algebra P.field.k S] [Algebra P.field.k T]
    (f : R →ₐ[P.field.k] S) (g : S →ₐ[P.field.k] T) (b : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace T b) (d : ℤ)
    (F : Sheaf (Spec (.of P.field.k)).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (h : (x ≫ continuityMap g.toRingHom b) ≫ continuityMap f.toRingHom b =
      x ≫ continuityMap (g.comp f).toRingHom b) :
    P.continuityGroundLeg f b (x ≫ continuityMap g.toRingHom b) d F ≫
        P.continuityGroundLeg g b x d F =
      eqToHom (congrArg (fun y ↦ (P.continuityGroundH R b y d).obj F) h) ≫
        P.continuityGroundLeg (g.comp f) b x d F := by
  sorry

end WeilConjectures.PurityFiniteSetting


namespace AlgebraicGeometry.Etale

/-- The published global-to-stalk map, derived at the module universe used in the
continuity diagram. Its underived map is the recorded coordinateGlobalToStalk.
Source: Stacks 09XP (blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityDerivedGlobalGerm (A : Type (u + 1)) [CommRing A]
    {Z X Z' T : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ T) [IsClosedImmersion i'] (f : T ⟶ X)
    (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    (coordinateGlobalSupport A i).rightDerivedFunctorPlus ⟶
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus ⋙
        (coordinateSupportedStalk A i' t).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := coordinateGlobalSupport A i) (G' := coordinateSupportedStalk A i' t)
      (β := upperStar (ModuleCat.{u + 1} A) f) (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ coordinateGlobalToStalk A i i' f hf t)

/-- All supported global classes commute with the supported pullback legs, including
ordered coordinate Kummer products and the empty product. Source: Stacks 09XP,
0EYM and the coordinate normalization
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: both underived composites have the ordinary composite germ as their composite
with the monic support inclusion. Kernel uniqueness identifies them. Derive using
exact inverse image and the normalized derived units; inverse-image associativity
is precisely the displayed final isomorphism. Taking cohomology gives the assertion
for every supported class, hence for the ordered Kummer class without a purity input. -/
theorem continuity_global_germ_composition (A : Type (u + 1)) [CommRing A]
    {Z X Z' T Z'' V : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (i'' : Z'' ⟶ V) [IsClosedImmersion i''] (f : T ⟶ X) (g : V ⟶ T)
    (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    (hg : Set.range i''.base = g.base ⁻¹' Set.range i'.base)
    (hgf : Set.range i''.base = (g ≫ f).base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ V)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (continuityDerivedGlobalGerm A i i' f hf (t ≫ g)).app K ≫
        (affineDerivedSupportGerm A i' i'' g hg t).app
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj K) =
      (continuityDerivedGlobalGerm A i i'' (g ≫ f) hgf t).app K ≫
        (coordinateSupportedStalk A i'' t).rightDerivedFunctorPlus.map
          ((coordinateDerivedPullbackComp A f g).inv.app K) := by
  sorry

end AlgebraicGeometry.Etale

namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry
variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- The image-stage functor for a map of affine bases. It is used only to describe
naturality, and is not assumed cofinal. Source: Stacks 0EYM, affine refinements
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityIndexMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra P.field.k R] [Algebra P.field.k S] (f : R →ₐ[P.field.k] S) :
    P.ContinuityIndex R ⥤ P.ContinuityIndex S where
  obj i := ⟨i.1.map f, i.2.map f⟩
  map a := homOfLE (Subalgebra.map_mono (show _ ≤ _ from leOfHom a))

/-- Restrict a base map to a stage and its image, retaining its actual algebra map.
Source: Stacks 0EYM (blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityStageMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra P.field.k R] [Algebra P.field.k S] (f : R →ₐ[P.field.k] S)
    (i : P.ContinuityIndex R) : i.1 →ₐ[P.field.k] ((P.continuityIndexMap f).obj i).1 :=
  (f.comp i.1.val).codRestrict (i.1.map f)
    (fun z ↦ Subalgebra.mem_map.mpr ⟨z, z.property, rfl⟩)

/-- Image points in the stage square agree.
Source: Stacks 0EYM, functoriality of affine space
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: the stage restriction followed by the image-subalgebra inclusion equals f
on every element. Apply Spec and AffineSpace.map, and associate the point composite. -/
theorem continuity_stage_square {R S : Type u} [CommRing R] [CommRing S]
    [Algebra P.field.k R] [Algebra P.field.k S] (f : R →ₐ[P.field.k] S) (b : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace S b) (i : P.ContinuityIndex R) :
    P.continuityPoint S b x ((P.continuityIndexMap f).obj i) ≫
        continuityMap (P.continuityStageMap f i).toRingHom b =
      P.continuityPoint R b (x ≫ continuityMap f.toRingHom b) i := by
  sorry

/-- The base-change map on one stage stalk, using its image-stage square.
Source: Stacks 0EYM, specified supported legs
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityBaseComponent {R S : Type u} [CommRing R] [CommRing S]
    [Algebra P.field.k R] [Algebra P.field.k S] (f : R →ₐ[P.field.k] S) (b : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace S b) (d : ℤ)
    (F : Sheaf (Spec (.of P.field.k)).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (i : P.ContinuityIndex R) :
    (P.continuityStage R b (x ≫ continuityMap f.toRingHom b) d i).obj F ⟶
      (P.continuityStage S b x d ((P.continuityIndexMap f).obj i)).obj F :=
  eqToHom (congrArg (fun y ↦ (P.continuityGroundH i.1 b y d).obj F)
    (P.continuity_stage_square f b x i).symm) ≫
  P.continuityGroundLeg (P.continuityStageMap f i) b
    (P.continuityPoint S b x ((P.continuityIndexMap f).obj i)) d F

/-- The base-change components respect transitions and the canonical limit legs.
Source: Stacks 0EYM, composition of the canonical exchanges
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: apply continuity_leg_composition to each of the two paths through the
image-subalgebra square. The algebra homomorphisms along both paths agree on elements;
transport of points and inverse-image associativity give the displayed equalities. -/
theorem continuity_base_laws {R S : Type u} [CommRing R] [CommRing S]
    [Algebra P.field.k R] [Algebra P.field.k S] (f : R →ₐ[P.field.k] S) (b : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace S b) (d : ℤ)
    (F : Sheaf (Spec (.of P.field.k)).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    (∀ (i j : P.ContinuityIndex R) (a : i ⟶ j),
      P.continuityTransition R b (x ≫ continuityMap f.toRingHom b) d F a ≫
          P.continuityBaseComponent f b x d F j =
        P.continuityBaseComponent f b x d F i ≫
          P.continuityTransition S b x d F ((P.continuityIndexMap f).map a)) ∧
    (∀ i : P.ContinuityIndex R,
      P.continuityBaseComponent f b x d F i ≫
          P.continuityLimitLeg S b x d F ((P.continuityIndexMap f).obj i) =
        P.continuityLimitLeg R b (x ≫ continuityMap f.toRingHom b) d F i ≫
          P.continuityGroundLeg f b x d F) := by
  sorry

/-- The natural map into the target colimit, defined by the canonical supported legs.
Source: Stacks 0EYM (blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityBaseCocone {R S : Type u} [CommRing R] [CommRing S]
    [Algebra P.field.k R] [Algebra P.field.k S] (f : R →ₐ[P.field.k] S) (b : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace S b) (d : ℤ)
    (F : Sheaf (Spec (.of P.field.k)).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    Cocone (P.continuityDiagram R b (x ≫ continuityMap f.toRingHom b) d F) where
  pt := colimit (P.continuityDiagram S b x d F)
  ι := {
    app i := P.continuityBaseComponent f b x d F i ≫
      colimit.ι (P.continuityDiagram S b x d F) ((P.continuityIndexMap f).obj i)
    naturality i j a := by
      change P.continuityTransition R b (x ≫ continuityMap f.toRingHom b) d F a ≫
        (P.continuityBaseComponent f b x d F j ≫
          colimit.ι (P.continuityDiagram S b x d F) ((P.continuityIndexMap f).obj j)) = _
      rw [← Category.assoc, (P.continuity_base_laws f b x d F).1 i j a]
      rw [Category.assoc]
      change _ ≫ (P.continuityDiagram S b x d F).map ((P.continuityIndexMap f).map a) ≫
        colimit.ι _ _ = _
      simp only [colimit.w, Functor.const_obj_map]
      exact (Category.comp_id _).symm }

/-- Naturality of continuity under an arbitrary map of affine k-algebras. Taking
S=R[1/f] gives localization compatibility, with no finite-type assumption on R.
Source: Stacks 0EYM and its affine-refinement argument
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: precompose with every colimit injection. Its images under the two sides are
the two canonical composite legs in continuity_base_laws. Those agree. Cofinality
then permits restricting to stages containing the localized element and its inverse;
the same equality proves agreement on any common principal affine refinement. -/
theorem continuity_base_change {R S : Type u} [CommRing R] [CommRing S]
    [Algebra P.field.k R] [Algebra P.field.k S] (f : R →ₐ[P.field.k] S) (b : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace S b) (d : ℤ)
    (F : Sheaf (Spec (.of P.field.k)).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    colimit.desc _ (P.continuityBaseCocone f b x d F) ≫
        P.continuityComparison S b x d F =
      P.continuityComparison R b (x ≫ continuityMap f.toRingHom b) d F ≫
        P.continuityGroundLeg f b x d F := by
  sorry

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.Etale

/-- The kernel inclusion is killed by the restriction unit after taking the stalk.
Source: Stacks 09XP (blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: kernel.condition is the zero composite of natural transformations. Whisker
that equation by the additive geometric stalk; it preserves zero morphisms. -/
theorem continuityStalkSequence_zero (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    coordinateSupportedStalkInclusion A i x ≫
      Functor.whiskerRight
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i.openComplement.ι).unit
        ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)) = 0 := by
  sorry

/-- The three terms of the support sequence at a geometric point, with the ordinary
restriction unit as its second map. Source: Stacks 0A45
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityStalkSequence (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      ModuleCat.{u + 1} A) :=
  ShortComplex.mk (coordinateSupportedStalkInclusion A i x)
    (Functor.whiskerRight
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i.openComplement.ι).unit
      ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)))
    (continuityStalkSequence_zero A i x)

/-- The stalk sequence is short exact on injectives. Source: Stacks 093X and 0A45
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: restriction of an injective to the complementary open has surjective unit
on sections, by etale_injective_support_sequence. The kernel is the recorded support
kernel. Exact geometric stalks preserve this short exact sequence. -/
theorem continuityStalkSequence_exact (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    (continuityStalkSequence A i x).ShortExactOnInjectives := by
  sorry

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- The complement of an inverse-image support maps into the original complement.
Source: Stacks 09XP (blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: a point in the new complement is outside the inverse image of the old closed
set. Its image is therefore in the old open complement, using the two complement
range equalities. -/
theorem continuity_complement_range {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base) :
    Set.range (i'.openComplement.ι ≫ f).base ⊆ Set.range i.openComplement.ι.base := by
  sorry

/-- The actual map between complementary opens.
Source: Stacks 09XP (blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityComplementMap {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base) :=
  IsOpenImmersion.lift i.openComplement.ι (i'.openComplement.ι ≫ f)
    (continuity_complement_range i i' f hf)

/-- The canonical commuting square for the complementary opens.
Source: Stacks 0EYM (blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: the open-immersion lift has composite i' .openComplement.ι followed by f,
by its defining factorization property. -/
theorem continuityComplementSquare {Z X Z' T : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i']
    (f : T ⟶ X) (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base) :
    CommSq (continuityComplementMap i i' f hf) i'.openComplement.ι i.openComplement.ι f :=
  by
  sorry

/-- Open direct-image exchange followed by inverse-image composition. This is the
ordinary third component used by the supported stalk localization sequence.
Source: Stacks 0EYM, canonical exchange, and 09XP
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityOpenExchange (A : Type (u + 1)) [CommRing A]
    {Z X Z' T : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ T) [IsClosedImmersion i'] (f : T ⟶ X)
    (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base) :
    upperStar (ModuleCat.{u + 1} A) i.openComplement.ι ⋙
      lowerStar (ModuleCat.{u + 1} A) i.openComplement.ι ⋙
      upperStar (ModuleCat.{u + 1} A) f ⟶
    upperStar (ModuleCat.{u + 1} A) f ⋙
      upperStar (ModuleCat.{u + 1} A) i'.openComplement.ι ⋙
      lowerStar (ModuleCat.{u + 1} A) i'.openComplement.ι :=
  Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) i.openComplement.ι)
      (baseChangeMap (ModuleCat.{u + 1} A) (continuityComplementSquare i i' f hf)) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (squareUpperStarIso (ModuleCat.{u + 1} A)
        (continuityComplementSquare i i' f hf)).inv
      (lowerStar (ModuleCat.{u + 1} A) i'.openComplement.ι)

/-- The third stalk component is exactly the ordinary open exchange above, conjugated
by the ordinary pullback-stalk identification.
Source: Stacks 0EYM and 0A45
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityOpenGerm (A : Type (u + 1)) [CommRing A]
    {Z X Z' T : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ T) [IsClosedImmersion i'] (f : T ⟶ X)
    (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    (continuityStalkSequence A i (t ≫ f)).X₃ ⟶
      upperStar (ModuleCat.{u + 1} A) f ⋙ (continuityStalkSequence A i' t).X₃ :=
  Functor.whiskerLeft
      (upperStar (ModuleCat.{u + 1} A) i.openComplement.ι ⋙
        lowerStar (ModuleCat.{u + 1} A) i.openComplement.ι)
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f t).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (continuityOpenExchange A i i' f hf)
      ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)) ≫
    (Functor.associator _ _ _).hom

/-- The prescribed three stalk maps commute with inclusion and restriction.
Source: Stacks 0A45 and 0EYM
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: the first equation is the defining kernel-inclusion equation of affineSupportGerm.
For the second, the open exchange is the adjunction mate of the square inverse-image
isomorphism. The mate identity sends the old restriction unit to the new restriction
unit. Apply the geometric stalk and its natural pullback identification. -/
theorem continuity_sequence_squares (A : Type (u + 1)) [CommRing A]
    {Z X Z' T : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ T) [IsClosedImmersion i'] (f : T ⟶ X)
    (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    (continuityStalkSequence A i (t ≫ f)).f ≫
        (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f t).inv =
      affineSupportGerm A i i' f hf t ≫ Functor.whiskerLeft
        (upperStar (ModuleCat.{u + 1} A) f) (continuityStalkSequence A i' t).f ∧
    (continuityStalkSequence A i (t ≫ f)).g ≫ continuityOpenGerm A i i' f hf t =
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f t).inv ≫ Functor.whiskerLeft
        (upperStar (ModuleCat.{u + 1} A) f) (continuityStalkSequence A i' t).g := by
  sorry

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Additivity of the ₁ term of the support stalk sequence.
Source: Stacks 09XP (blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
instance continuityStalkSequence_additive₁ (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    (continuityStalkSequence A i t).X₁.Additive :=
  inferInstanceAs (coordinateSupportedStalk A i t).Additive

/-- Additivity of the ₂ term of the support stalk sequence.
Source: Stacks 09XP (blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
instance continuityStalkSequence_additive₂ (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    (continuityStalkSequence A i t).X₂.Additive :=
  inferInstanceAs (((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A))).Additive

/-- Additivity of the ₃ term of the support stalk sequence.
Source: Stacks 09XP (blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
instance continuityStalkSequence_additive₃ (A : Type (u + 1)) [CommRing A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ X) :
    (continuityStalkSequence A i t).X₃.Additive :=
  inferInstanceAs ((upperStar (ModuleCat.{u + 1} A) i.openComplement.ι ⋙
      lowerStar (ModuleCat.{u + 1} A) i.openComplement.ι ⋙
      ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)))).Additive

/-- The comparison of support sequences on actual injective models. Its third map
uses the ordinary open exchange, so the boundary equation below also specifies the
higher-direct-image exchanges in the node.
Source: Stacks 0EYM and 0A45
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityResolutionMap (A : Type (u + 1)) [CommRing A]
    {Z X Z' T : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ T) [IsClosedImmersion i'] (f : T ⟶ X)
    (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (c : ((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj I ⟶ J) :
    (continuityStalkSequence A i (t ≫ f)).mapCochainComplex I ⟶
      (continuityStalkSequence A i' t).mapCochainComplex J :=
  ShortComplex.mapCochainComplexPullback
    (upperStar (ModuleCat.{u + 1} A) f)
    (affineSupportGerm A i i' f hf t)
    (upperStarCompSheafFiberIso (ModuleCat.{u + 1} A) f t).inv
    (continuityOpenGerm A i i' f hf t)
    (continuity_sequence_squares A i i' f hf t).1
    (continuity_sequence_squares A i i' f hf t).2 I J c

/-- The localization boundary commutes with the canonical supported and open legs.
This equation is on degreewise-injective resolutions, which compute the bounded-below
right derived functors and their cohomology maps used in continuityComparison.
Source: Stacks 0A45 and Tag 0152, naturality of the connecting map
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: continuityStalkSequence_exact gives short exact sequences on both injective
complexes. continuity_sequence_squares gives their canonical comparison with three
components. Apply triangleOfSESδ_naturality to continuityResolutionMap. Passing to
homotopy and taking cohomology identifies these maps with affineDerivedSupportGerm
and the higher-direct-image exchanges by their derived-unit normalization. -/
theorem continuity_localization_boundary (A : Type (u + 1)) [CommRing A]
    {Z X Z' T : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ T) [IsClosedImmersion i'] (f : T ⟶ X)
    (hf : Set.range i'.base = f.base ⁻¹' Set.range i.base)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (J : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [∀ n : ℤ, Injective (I.X n)] [∀ n : ℤ, Injective (J.X n)]
    (c : ((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj I ⟶ J) :
    DerivedCategory.triangleOfSESδ
        ((continuityStalkSequence_exact A i (t ≫ f)).shortExact_mapCochainComplex I) ≫
      (DerivedCategory.Q.map (continuityResolutionMap A i i' f hf t I J c).τ₁)⟦(1 : ℤ)⟧' =
    DerivedCategory.Q.map (continuityResolutionMap A i i' f hf t I J c).τ₃ ≫
      DerivedCategory.triangleOfSESδ
        ((continuityStalkSequence_exact A i' t).shortExact_mapCochainComplex J) := by
  sorry

end AlgebraicGeometry.Etale

namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry
variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- Exact identification with the displayed geometric stalk of H^d(RQ(A(r))).
Source: Stacks 09XP, exactness of geometric stalks
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuitySupportedSheafStalkIso (R : Type u) [CommRing R] (b : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R b) (r d : ℤ) :
    P.continuityStalk R b x r d ≅
      ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} P.Coefficient)).obj
        ((DerivedCategory.Plus.homologyFunctor _ d).obj
          ((Etale.coordinateSupportSheaf P.Coefficient
            (continuityOrigin R b)).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj (P.continuityTwist R b r)))) :=
  (DerivedCategory.Plus.homologyFunctor _ d).mapIso
      ((Functor.rightDerivedFunctorPlusCompIso
        (Etale.coordinateSupportSheaf P.Coefficient (continuityOrigin R b))
        ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} P.Coefficient)) ≪≫
        Functor.isoWhiskerLeft _
          (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
            ((Scheme.pointSmallEtale x).sheafFiber
              (A := ModuleCat.{u + 1} P.Coefficient)))).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (P.continuityTwist R b r))) ≪≫
    (((Scheme.pointSmallEtale x).sheafFiber
      (A := ModuleCat.{u + 1} P.Coefficient)).mapDerivedCategoryPlusHomologyFunctorIso d).symm.app
          ((Etale.coordinateSupportSheaf P.Coefficient
            (continuityOrigin R b)).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj (P.continuityTwist R b r)))

/-- Stages containing a prescribed element, with the inherited directed ordering.
Source: Stacks 0EYM, localization refinement
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
abbrev ContinuityContaining (R : Type u) [CommRing R] [Algebra P.field.k R] (s : R) :=
  {i : P.ContinuityIndex R // s ∈ i.1}

/-- The canonical inclusion of stages containing the localized element.
Source: Stacks 0EYM (blueprint: lem-pur-affine-coordinate-support-stalk-continuity). -/
def continuityContainingInclusion (R : Type u) [CommRing R] [Algebra P.field.k R] (s : R) :
    P.ContinuityContaining R s ⥤ P.ContinuityIndex R where
  obj i := i.1
  map a := homOfLE (show _ ≤ _ from leOfHom a)

/-- Restricting to stages containing the element is final and directed.
Source: Stacks 0EYM, localization clause
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: adjoin s to any finite generating set. This gives a finite subalgebra containing
s above any given stage. Adjoining the union of two finite generating sets gives an
upper bound still containing s. The subposet is nonempty and every over-category of
its inclusion is nonempty and directed, hence connected; this is finality. -/
theorem continuity_containing_final (R : Type u) [CommRing R] [Algebra P.field.k R]
    (s : R) :
    (P.continuityContainingInclusion R s).Final ∧
      Nonempty (P.ContinuityContaining R s) ∧
      IsDirected (P.ContinuityContaining R s) (· ≤ ·) := by
  sorry

/-- Full support in dimension zero: all nonzero cohomological degrees vanish, and
the comparison in degree zero is the ordinary constant-line comparison.
Source: Stacks 09XP, empty complementary open
(blueprint: lem-pur-affine-coordinate-support-stalk-continuity).
Proof: with no coordinates the zero section is the whole space. The complementary
open is empty, its direct image is zero, and its unit has zero target. Thus the
support kernel is canonically the identity, compatibly with its inclusion. Derivation
and exact stalks give the degree-zero fibre and zero in all other degrees. The
canonical legs are the identity of the pulled-back constant line; their filtered
colimit is that line. The empty ordered Kummer product is the unit and all open
boundary maps are zero. -/
theorem continuity_zero_coordinates (R : Type u) [CommRing R] [Algebra P.field.k R]
    (r : ℤ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ continuitySpace R 0) :
    (∀ d : ℤ, d ≠ 0 → IsZero (P.continuityStalk R 0 x r d)) ∧
    Nonempty (P.continuityStalk R 0 x r 0 ≅
      ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} P.Coefficient)).obj
        (P.continuityTwist R 0 r)) ∧
    IsIso (P.continuityComparison R 0 x 0
      (P.functorialCupTwist false (Spec (.of P.field.k)) r)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
