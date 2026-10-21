/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
public import Sheaf.Paper.OrientedProductPointsConservative
public import Sheaf.TraceFormula.FiniteBaseStrictLocalization
public import Sheaf.TraceFormula.OrientedPointCohomology
public import Sheaf.Paper.OrientedNearbyStrictLocalDescription
public import Sheaf.Paper.OrientedHypercoverDescentDatum
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
import Sheaf.AlgebraicGeometry.FiniteBaseCechComponents
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.StrictHenselizationFunctoriality

/-!
# Finite-cover tube decomposition and the ordinary comparison

Source: Orgogozo, Modifications et cycles proches sur une base générale,
Lemmas 2.6 and 2.6.1, printed pp. 4--5
(blueprint: lem-trf-finite-cover-tube-comparison).

## Main definitions

* `Change.tubeMap`, `restriction` and `tubeRestriction`: the canonical geometric
  and derived restriction maps, retaining the ordinary adjunction normalization.
* `pointCohomology`: the point-cohomology restriction in the strict-local stalk model.
* `LiftedPoint`: the finite-local-factor specialization, without choosing its field.
* `cechMap`, `coverCoface` and `coverAugmentation`: the actual augmented Cech restrictions.

## Main statements

* `ordinaryComparison`: the ordinary nearby-cycle comparison is tube restriction.
* `finiteTubeDecomposition` and `finiteSectionDecomposition`: canonical finite
  coproduct and product cones, with their specified inclusions and restrictions.
* `coverRestriction_ordinaryComparisons`: the product coordinates are the actual
  ordinary comparison stalks for the Cartesian cover squares.
* `coverRestriction_coface` and `coverRestriction_augmentation`: compatibility
  with all Cech structure maps and the two augmentations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.AdicSites
open AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.OrientedNearbyCycles.FiniteCoverTubeComparison

/-- The point and its specified specialization, with the original geometric fields.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
structure Point {X S : Scheme.{u}} (f : X ⟶ S)
    (Ω Ξ : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ] where
  x : Spec (.of Ω) ⟶ X
  b : Spec (.of Ξ) ⟶ S
  c : Scheme.strictHenselizationScheme b ⟶ Scheme.strictHenselizationScheme (x ≫ f)
  over : c ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
    Scheme.strictHenselizationStructuralMap b

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
  {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]

/-- The tube with its actual specialization arrow, not an arbitrary scheme.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
abbrev tube (z : Point f Ω Ξ) := pullback (Scheme.strictHenselizationMap f z.x) z.c

/-- The structure map of the tube to the source scheme.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def toSource (z : Point f Ω Ξ) : tube z ⟶ X :=
  pullback.fst _ _ ≫ Scheme.strictHenselizationStructuralMap z.x

/-- The tube is over the strict localization at f(x).
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def toBase (z : Point f Ω Ξ) : tube z ⟶ Scheme.strictHenselizationScheme (z.x ≫ f) :=
  pullback.snd _ _ ≫ z.c

/-- The geometric lift of b along the specified specialization.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def basePoint (z : Point f Ω Ξ) :
    Spec (.of Ξ) ⟶ Scheme.strictHenselizationScheme (z.x ≫ f) :=
  strictLocalPoint z.b ≫ z.c

/-- A point over a point, including the compatibility of the actual specializations.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
structure Change (z : Point f Ω Ξ) (z' : Point f' Ω Ξ)
    (h : X' ⟶ X) (g : S' ⟶ S) (w : h ≫ f = f' ≫ g) where
  x_over : z'.x ≫ h = z.x
  b_over : z'.b ≫ g = z.b
  specialization :
    Scheme.strictHenselizationMap g z'.b ≫
        eqToHom (congrArg Scheme.strictHenselizationScheme b_over) ≫ z.c =
      z'.c ≫ Scheme.strictHenselizationMap g (z'.x ≫ f') ≫
        eqToHom (congrArg Scheme.strictHenselizationScheme
          ((Category.assoc z'.x f' g).trans
            ((congrArg (fun k ↦ z'.x ≫ k) w.symm).trans
              ((Category.assoc z'.x h f).symm.trans
                (congrArg (fun k ↦ k ≫ f) x_over)))))

/-- The canonical strict-local map on source factors.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def Change.sourceMap {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w) :=
  Scheme.strictHenselizationMap h z'.x ≫
    eqToHom (congrArg Scheme.strictHenselizationScheme d.x_over)

/-- The canonical strict-local map on the generizing base factors.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def Change.genericMap {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w) :=
  Scheme.strictHenselizationMap g z'.b ≫
    eqToHom (congrArg Scheme.strictHenselizationScheme d.b_over)

/-- The two projected maps defining the tube restriction agree.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: strict-local functoriality for the commutative square identifies its two source
composites. Compose that equation with the defining tube pullback equation and use
Change.specialization. This gives exactly the displayed equality. -/
theorem Change.tube_condition {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w) :
    (pullback.fst (Scheme.strictHenselizationMap f' z'.x) z'.c ≫ d.sourceMap) ≫
        Scheme.strictHenselizationMap f z.x =
      (pullback.snd (Scheme.strictHenselizationMap f' z'.x) z'.c ≫ d.genericMap) ≫ z.c := by
  sorry

/-- The natural tube map, constructed by the fibre-product universal property.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def Change.tubeMap {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w) :
    tube z' ⟶ tube z :=
  pullback.lift (pullback.fst _ _ ≫ d.sourceMap)
    (pullback.snd _ _ ≫ d.genericMap) d.tube_condition

/-- The geometric point of the vanishing topos, using the published strict-local section.
The point of S_(f(x)) is precisely the lift of b by c.
Source: Orgogozo, Lemma 2.6; Illusie 1.11
(blueprint: lem-trf-finite-cover-tube-comparison). -/
def pointModules (z : Point f Ω Ξ) :=
  moduleMorphism (vanishingDatum.{u, u + 1} f) punctualSite.{u + 1}
    ((geometricEtalePoint.{u, u + 1} (basePoint z)).comp
      (strictLocalSigma.{u, u + 1} f z.x))

/-- The geometric morphism from a scheme's etale topos to the punctual presentation.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def epsilon (Y : Scheme.{u}) :
    GeometricMorphism (Sheaf (etaleTopology.{u, u + 1} Y) (Type (u + 1)))
      (Sheaf punctualSite.{u + 1}.topology (Type (u + 1))) where
  inverse := punctualEquivalence.{u + 1}.functor ⋙ (localEpsilon.{u, u + 1} Y).inverse
  direct := (localEpsilon.{u, u + 1} Y).direct ⋙ punctualEquivalence.{u + 1}.inverse
  adj := punctualEquivalence.toAdjunction.comp (localEpsilon Y).adj
  leftExact := by
    have := (localEpsilon.{u, u + 1} Y).leftExact
    infer_instance

/-- Global sections as the actual constant-module direct image to the punctual site.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def sectionModules (Y : Scheme.{u}) :=
  moduleMorphism punctualSite.{u + 1} (etaleDatum.{u, u + 1} Y) (epsilon Y)

/-- RΓ, with the constant-module/K-injective construction used for nearby cycles.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
abbrev sections (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :=
  (sectionModules Y).push (Coeff.{u, u + 1} Λ)

/-- Direct-image sections commute with a scheme map, with the terminal-section
normalization of localDirectSections.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def epsilonSquare {Y Z : Scheme.{u}} (a : Y ⟶ Z) :
    ((epsilon Y).comp (identity _)).direct ≅
      ((etaleMorphism.{u, u + 1} a).comp (epsilon Z)).direct :=
  Functor.rightUnitor _ ≪≫
    Functor.isoWhiskerRight (localDirectSections.{u, u + 1} a).symm
      punctualEquivalence.{u + 1}.inverse ≪≫ Functor.associator _ _ _

/-- The exact inverse-image square for the global-section adjunctions.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def sectionSquare {Y Z : Scheme.{u}} (a : Y ⟶ Z)
    (Λ : Type (u + 1)) [CommRing Λ] :
    (sectionModules Y).pull (Coeff.{u, u + 1} Λ) ≅
      (sectionModules Z).pull (Coeff Λ) ⋙ (etaleModules a).pull (Coeff Λ) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (strictLocalIdentityPull punctualSite (Coeff Λ)).symm _ ≪≫
    derivedSquare (f := sectionModules Z)
      (g := moduleMorphism punctualSite punctualSite (identity _))
      (h := etaleModules a) (k := sectionModules Y)
      (GeometricMorphism.inverseIso (epsilonSquare a)).symm (Coeff Λ)

/-- Actual derived restriction: the adjoint transpose of pullback of the counit.
Its ordinary normalization is the terminal-section restriction in epsilonSquare.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def restriction {Y Z : Scheme.{u}} (a : Y ⟶ Z)
    (Λ : Type (u + 1)) [CommRing Λ] (L : EtaleDerived.{u, u + 1} Z Λ) :
    (sections Z Λ).obj L ⟶
      (sections Y Λ).obj (((etaleModules.{u, u + 1} a).pull (Coeff Λ)).obj L) :=
  ((sectionModules Y).adj (Coeff Λ)).homEquiv _ _
    ((sectionSquare a Λ).hom.app ((sections Z Λ).obj L) ≫
      ((etaleModules a).pull (Coeff Λ)).map (((sectionModules Z).adj (Coeff Λ)).counit.app L))

/-- Derived sections of the specified tube, with coefficients restricted from X.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
abbrev tubeSections (z : Point f Ω Ξ) (Λ : Type (u + 1)) [CommRing Λ]
    (K : EtaleDerived.{u, u + 1} X Λ) :=
  (sections (tube z) Λ).obj
    (((etaleModules.{u, u + 1} (toSource z)).pull (Coeff Λ)).obj K)

/-- Pullback of coefficients along an over-X map, using the published normalized
composition comparison and the given over-X equation.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def coefficientMap {Y Z : Scheme.{u}} (a : Y ⟶ Z) (r : Z ⟶ X) (s : Y ⟶ X)
    (w : a ≫ r = s) (Λ : Type (u + 1)) [CommRing Λ]
    (K : EtaleDerived.{u, u + 1} X Λ) :
    ((etaleModules.{u, u + 1} a).pull (Coeff Λ)).obj
        (((etaleModules r).pull (Coeff Λ)).obj K) ⟶
      ((etaleModules s).pull (Coeff Λ)).obj K :=
  (Hypercover.pullComposition r a Λ).hom.app K ≫
    eqToHom (congrArg (fun t ↦ ((etaleModules.{u, u + 1} t).pull (Coeff Λ)).obj K) w)

/-- Restriction of coefficients from a fixed scheme, including the canonical
composition identification. This is the map used in the augmented Cech diagrams.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def restrictionOver {Y Z : Scheme.{u}} (a : Y ⟶ Z) (r : Z ⟶ X) (s : Y ⟶ X)
    (w : a ≫ r = s) (Λ : Type (u + 1)) [CommRing Λ]
    (K : EtaleDerived.{u, u + 1} X Λ) :
    (sections Z Λ).obj (((etaleModules.{u, u + 1} r).pull (Coeff Λ)).obj K) ⟶
      (sections Y Λ).obj (((etaleModules s).pull (Coeff Λ)).obj K) :=
  restriction a Λ (((etaleModules r).pull (Coeff Λ)).obj K) ≫
    (sections Y Λ).map (coefficientMap a r s w Λ K)

/-- Leray for global sections, as the conjugate of the actual constant-inverse-image
square; all adjunctions and their normalization are the previously fixed ones.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def sectionsPushIso {Y Z : Scheme.{u}} (a : Y ⟶ Z)
    (Λ : Type (u + 1)) [CommRing Λ] :
    (etaleModules.{u, u + 1} a).push (Coeff Λ) ⋙ sections Z Λ ≅ sections Y Λ :=
  (conjugateIsoEquiv
    (((sectionModules Z).adj (Coeff Λ)).comp ((etaleModules a).adj (Coeff Λ)))
    ((sectionModules Y).adj (Coeff Λ))) (sectionSquare a Λ)

/-- The exact geometric stalk model: restrict sigma_x along c, then take sections on
S_(b). Sections on this strictly local scheme are its closed-geometric-point stalk.
Thus this is the point (x,b,c), with no choice of a comparison isomorphism.
Source: Orgogozo, Lemma 2.6; Illusie 1.11; Stacks 03Q9
(blueprint: lem-trf-finite-cover-tube-comparison). -/
def stalk (z : Point f Ω Ξ) (Λ : Type (u + 1)) [CommRing Λ] :
    VanishingDerived.{u, u + 1} f Λ ⥤
      punctualSite.{u + 1}.derived (Coeff.{u, u + 1} Λ) :=
  (strictLocalSigmaModules.{u, u + 1} f z.x).pull (Coeff Λ) ⋙
    (etaleModules.{u, u + 1} z.c).pull (Coeff Λ) ⋙
      sections (Scheme.strictHenselizationScheme z.b) Λ

/-- The canonical point-cohomology map, in the strict-local stalk model. It is the
strict-local description, ordinary direct-image base change along c, and Leray for
sections, followed by the canonical coefficient-composition comparison.
In particular it has the restriction normalization of orientedPointCohomology.
Source: Orgogozo, Lemma 2.6; Illusie 1.3, 1.11
(blueprint: lem-trf-finite-cover-tube-comparison). -/
def pointCohomology (z : Point f Ω Ξ) (Λ : Type (u + 1)) [CommRing Λ]
    (K : EtaleDerived.{u, u + 1} X Λ) :
    (stalk z Λ).obj ((nearbyCycles f Λ).obj K) ⟶ tubeSections z Λ K :=
  (sections (Scheme.strictHenselizationScheme z.b) Λ).map
      (((etaleModules.{u, u + 1} z.c).pull (Coeff Λ)).map
        ((strictLocalDescriptionComparison.{u, u + 1} f z.x Λ).app K)) ≫
    (sections (Scheme.strictHenselizationScheme z.b) Λ).map
      (strictLocalDirectBaseChange.{u, u + 1} (Scheme.strictHenselizationMap f z.x)
        (pullback.snd _ _) (pullback.fst _ _) z.c pullback.condition Λ
        (((etaleModules.{u, u + 1} (Scheme.strictHenselizationStructuralMap z.x)).pull
          (Coeff Λ)).obj K)) ≫
    (sectionsPushIso (pullback.snd (Scheme.strictHenselizationMap f z.x) z.c) Λ).hom.app
      (((etaleModules.{u, u + 1} (pullback.fst _ _)).pull (Coeff Λ)).obj
        (((etaleModules.{u, u + 1} (Scheme.strictHenselizationStructuralMap z.x)).pull
          (Coeff Λ)).obj K)) ≫
    (sections (tube z) Λ).map
      ((Hypercover.pullComposition (Scheme.strictHenselizationStructuralMap z.x)
        (pullback.fst _ _) Λ).hom.app K)

/-- The canonical tube map is over the original source map.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: its first projection is the functorial strict-local map on X. Compose with the
structural map, use strictHenselizationMap_over and x_over, and reassociate. -/
theorem Change.tubeMap_over {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w) :
    d.tubeMap ≫ toSource z = toSource z' ≫ h := by
  sorry

/-- The actual restriction on tubes, including the canonical identification of the
pullback of K on the changed source.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def tubeRestriction {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived.{u, u + 1} X Λ) :
    tubeSections z Λ K ⟶
      tubeSections z' Λ (((etaleModules.{u, u + 1} h).pull (Coeff Λ)).obj K) :=
  restrictionOver d.tubeMap (toSource z) (toSource z' ≫ h) d.tubeMap_over Λ K ≫
    (sections (tube z') Λ).map
      ((Hypercover.pullComposition h (toSource z') Λ).inv.app K)

/-- The image specialization in a commutative square. Its first two points are the
composite geometric points, and its third datum is the specified compatible c.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
structure Image (h : X' ⟶ X) (g : S' ⟶ S) (w : h ≫ f = f' ≫ g)
    (z' : Point f' Ω Ξ) where
  c : Scheme.strictHenselizationScheme (z'.b ≫ g) ⟶
    Scheme.strictHenselizationScheme ((z'.x ≫ h) ≫ f)
  over : c ≫ Scheme.strictHenselizationStructuralMap ((z'.x ≫ h) ≫ f) =
    Scheme.strictHenselizationStructuralMap (z'.b ≫ g)
  comm : Scheme.strictHenselizationMap g z'.b ≫ c =
    z'.c ≫ strictLocalSquareBase f f' h g w z'.x

/-- The image oriented point, with its original composite geometric fields.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def Image.point {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g}
    {z' : Point f' Ω Ξ} (d : Image h g w z') : Point f Ω Ξ :=
  ⟨z'.x ≫ h, z'.b ≫ g, d.c, d.over⟩

/-- The canonical image-point identification on stalks. This is restriction along the
pointed local map S'_(b') to S_(b), with the sigma square and c-square inserted.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def Image.stalkRestriction {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g}
    {z' : Point f' Ω Ξ} (d : Image h g w z')
    (Λ : Type (u + 1)) [CommRing Λ] (L : VanishingDerived.{u, u + 1} f Λ) :
    (stalk d.point Λ).obj L ⟶
      (stalk z' Λ).obj (((squareModules.{u, u + 1} f f' h g w).pull (Coeff Λ)).obj L) :=
  restriction (Scheme.strictHenselizationMap g z'.b) Λ
      (((etaleModules.{u, u + 1} d.c).pull (Coeff Λ)).obj
        (((strictLocalSigmaModules.{u, u + 1} f (z'.x ≫ h)).pull (Coeff Λ)).obj L)) ≫
    (sections (Scheme.strictHenselizationScheme z'.b) Λ).map
      ((strictLocalDirectSquare.{u, u + 1} d.c z'.c
        (Scheme.strictHenselizationMap g z'.b)
        (strictLocalSquareBase f f' h g w z'.x) d.comm Λ).inv.app
          (((strictLocalSigmaModules.{u, u + 1} f (z'.x ≫ h)).pull (Coeff Λ)).obj L)) ≫
    (sections (Scheme.strictHenselizationScheme z'.b) Λ).map
      (((etaleModules.{u, u + 1} z'.c).pull (Coeff Λ)).map
        ((strictLocalSigmaPullSquare.{u, u + 1} f f' h g w z'.x Λ).inv.app L))

/-- The image-point identification in arbitrary coordinates on the geometric points.
Only substitution along the two image-point equalities is used.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def Change.stalkRestriction {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    (Λ : Type (u + 1)) [CommRing Λ] (L : VanishingDerived.{u, u + 1} f Λ) :
    (stalk z Λ).obj L ⟶
      (stalk z' Λ).obj (((squareModules.{u, u + 1} f f' h g w).pull (Coeff Λ)).obj L) := by
  rcases z with ⟨x, b, c, hc⟩
  rcases d with ⟨hx, hb, hw⟩
  cases hx
  cases hb
  exact Image.stalkRestriction ⟨c, hc, hw⟩ Λ L

/-- A finite-cover geometric component is indexed by the unique lift with the field of b.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
abbrev Index (z : Point f Ω Ξ) {P : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) :=
  {t : Spec (.of Ξ) ⟶ P // t ≫ p = basePoint z}

/-- The canonical map from geometric lifts to geometric-fibre connected components.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def componentIndex (z : Point f Ω Ξ) {P : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) (t : Index z p) :=
  ConnectedComponents.mk
    ((pullback.lift t.val (𝟙 _) (t.property.trans (Category.id_comp _).symm))
      (IsLocalRing.closedPoint Ξ))

/-- The base-changed morphism X_P to P.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
abbrev coverMorphism (z : Point f Ω Ξ) {P : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) :=
  pullback.snd f (p ≫ Scheme.strictHenselizationStructuralMap (z.x ≫ f))

/-- The finite cover of the tube at one Cech degree.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
abbrev coverTube (z : Point f Ω Ξ) {P : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) := pullback (toBase z) p

/-- Its canonical source map to X.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def coverSource (z : Point f Ω Ξ) {P : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) : coverTube z p ⟶ X :=
  pullback.fst _ _ ≫ toSource z

/-- The lifted specialization, including its strict-local finite factor. The closed
point has the field of x, the generizing point has the field of b, and the structural
map of the first strict localization is the open-and-closed factor inclusion.
Source: Orgogozo, Lemma 2.6.1; Stacks 04GH, 0GIP
(blueprint: lem-trf-finite-cover-tube-comparison). -/
structure LiftedPoint (z : Point f Ω Ξ) {P : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) (t : Index z p) where
  point : Point (coverMorphism z p) Ω Ξ
  generic_eq : point.b = t.val
  change : Change z point (pullback.fst _ _)
    (p ≫ Scheme.strictHenselizationStructuralMap (z.x ≫ f)) pullback.condition
  closed_over : (point.x ≫ coverMorphism z p) ≫ p = strictLocalPoint (z.x ≫ f)
  factor_open : IsOpenImmersion
    (Scheme.strictHenselizationStructuralMap (point.x ≫ coverMorphism z p))
  factor_closed : IsClosedImmersion
    (Scheme.strictHenselizationStructuralMap (point.x ≫ coverMorphism z p))

/-- The two canonical maps from a lifted tube agree over S_0.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: compose the two tube projections with the specialization structural equation.
Functoriality of the strict-local source map and change.specialization identify the
resulting maps to S_0; the original finite base-change square identifies their maps to P. -/
theorem LiftedPoint.inclusion_condition {z : Point f Ω Ξ} {P : Scheme.{u}}
    {p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)} {t : Index z p}
    (l : LiftedPoint z p t) :
    l.change.tubeMap ≫ toBase z = (toSource l.point ≫ coverMorphism z p) ≫ p := by
  sorry

/-- The component inclusion, with both projections fixed by their constructions.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def LiftedPoint.inclusion {z : Point f Ω Ξ} {P : Scheme.{u}}
    {p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)} {t : Index z p}
    (l : LiftedPoint z p t) : tube l.point ⟶ coverTube z p :=
  pullback.lift l.change.tubeMap (toSource l.point ≫ coverMorphism z p)
    l.inclusion_condition

/-- The component inclusion is over X.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: use the first projection equation of pullback.lift and change.tubeMap_over. -/
theorem LiftedPoint.inclusion_over {z : Point f Ω Ξ} {P : Scheme.{u}}
    {p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)} {t : Index z p}
    (l : LiftedPoint z p t) :
    l.inclusion ≫ coverSource z p = toSource l.point ≫ pullback.fst _ _ := by
  sorry

/-- Sections A_q (or B_q) on a finite cover of a tube.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
abbrev coverSections (z : Point f Ω Ξ) {P : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived.{u, u + 1} X Λ) :=
  (sections (coverTube z p) Λ).obj
    (((etaleModules.{u, u + 1} (coverSource z p)).pull (Coeff Λ)).obj K)

/-- The component restriction to its actual nearby-cycle tube, with K pulled back to X_P.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def LiftedPoint.sectionRestriction {z : Point f Ω Ξ} {P : Scheme.{u}}
    {p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)} {t : Index z p}
    (l : LiftedPoint z p t) (Λ : Type (u + 1)) [CommRing Λ]
    (K : EtaleDerived.{u, u + 1} X Λ) :
    coverSections z p Λ K ⟶ tubeSections l.point Λ
      (((etaleModules.{u, u + 1} (pullback.fst f
        (p ≫ Scheme.strictHenselizationStructuralMap (z.x ≫ f)))).pull (Coeff Λ)).obj K) :=
  restrictionOver l.inclusion (coverSource z p) (toSource l.point ≫ pullback.fst _ _)
      l.inclusion_over Λ K ≫
    (sections (tube l.point) Λ).map
      ((Hypercover.pullComposition (pullback.fst _ _) (toSource l.point) Λ).inv.app K)

/-- The finite disjoint-union decomposition of a tube after a finite base cover.
The index bijection is the actual geometric-fibre component map. The factors in the
cofan are precisely the lifted-specialization tubes, and its maps are the canonical
inclusions, so the universal property specifies the claimed coproduct identification.
Source: Orgogozo, Lemmas 2.6 and 2.6.1; Stacks 04GH, 0GIP
(blueprint: lem-trf-finite-cover-tube-comparison).

Proof:
1. Identify S_(b) over S_0 with the strict localization of S_0 at basePoint z, by
ind-etale invariance and strict-local functoriality.
2. Apply finite_strictLocalization_decomposition at this point. Its geometric lifts
are exactly Index z p, and its bijection is componentIndex.
3. Apply the same lemma at the closed point of S_0. It gives the finite open-and-closed
strictly local factors H. Each generic lift lies in a unique factor. Its closed point
has a unique lift with the field of x because the residue extension is finite purely
inseparable. The structural map from the generic strict localization factors through H.
4. Use finite_strictLocalization_isPullback and the strict-base closed-point localization
lemma to identify the strict localization of X_P with X_(x) times that factor. Pulling
along the generic specialization cancels the factor and gives tube l.point.
5. Base-changing the coproduct of step 2 along X_(x) and reassociating fibre products
gives the cofan below. Its two projections are inclusion's projections, hence its
identification is the canonical one. Empty fibres give the empty coproduct as well. -/
theorem finiteTubeDecomposition (z : Point f Ω Ξ) {P : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) [IsFinite p] :
    Finite (Index z p) ∧ Function.Bijective (componentIndex z p) ∧
      ∃ l : ∀ t : Index z p, LiftedPoint z p t,
        Nonempty (IsColimit (Cofan.mk (coverTube z p) (fun t ↦ (l t).inclusion))) := by
  sorry

/-- The corresponding canonical finite-product description of derived sections.
The product cone consists of the actual restriction maps, not arbitrary projections
or an isomorphism of unlabelled objects.
Source: Orgogozo, Lemmas 2.6 and 2.6.1
(blueprint: lem-trf-finite-cover-tube-comparison).

Proof: finiteTubeDecomposition gives the finite disjoint union. Sections are products
of the component sections. Finite products of module complexes are finite sums and
are exact, so this statement survives K-injective derivation. Restriction and the
normalized pullComposition identify its cone maps with sectionRestriction. -/
theorem finiteSectionDecomposition (z : Point f Ω Ξ) {P : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) [IsFinite p]
    (l : ∀ t : Index z p, LiftedPoint z p t)
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived.{u, u + 1} X Λ) :
    Nonempty (IsLimit (Fan.mk (coverSections z p Λ K)
      (fun t ↦ (l t).sectionRestriction Λ K))) := by
  sorry

/-- The point-cohomology comparison is the normalized restriction isomorphism of
orientedPointCohomology in the strict-local presentation used here.
Source: Orgogozo, Lemma 2.6; Illusie 1.3
(blueprint: lem-trf-finite-cover-tube-comparison).

Proof: on a pointed triple (E to V from W), the counit underlying the strict-local
description restricts to E times_V W. Restriction along c and the direct-image mate
then restrict to its map from the inverse-limit tube. Leray and pullComposition do
not change this section map. Thus pointCohomology is exactly the transformation
normalized by sourceUnit and targetUnit in orientedPointCohomology, after canonical
site and constant-ring transports. That theorem makes it invertible for bounded-below
K; the displayed boundedness implies bounded-below. No base-change invertibility is used. -/
theorem pointCohomology_isIso [LocallyOfFiniteType f] [QuasiCompact f]
    (z : Point f Ω Ξ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [HasInvertibleExponent Λ S] (K : EtaleDerived.{u, u + 1} X Λ)
    (_hKb : IsBounded (etaleDatum.{u, u + 1} X) (Coeff.{u, u + 1} Λ) K)
    (_hKc : ∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((Hypercover.readModules X Λ).obj
        ((DerivedCategory.homologyFunctor _ n).obj K))) :
    IsIso (pointCohomology z Λ K) := by
  sorry

/-- The image-point stalk identification is invertible, independently of the nearby
comparison. The only map used here is the pointed local map between strict local bases.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: global sections on each strictly local base are the closed-point stalk. The
canonical local strict-henselization map preserves the indicated geometric point, so
restriction identifies with the identity stalk comparison. The sigma and c squares
are normalized isomorphisms. All these functors are exact, hence so is their derived
identification; apply it to any unbounded L. -/
theorem Change.stalkRestriction_isIso {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    (Λ : Type (u + 1)) [CommRing Λ] (L : VanishingDerived.{u, u + 1} f Λ) :
    IsIso (d.stalkRestriction Λ L) := by
  sorry

/-- The stalk of the actual ordinary comparison beta is restriction on the two tubes.
All four arrows are specified constructions: pointCohomology has the recorded pointed-
triple restriction normalization, and stalkRestriction is the image-point identification.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison).

Proof:
1. Strict-local functoriality and the fibre-product property construct tubeMap.
2. On a pointed triple (E to V from W), the transpose of the counit defining beta
sends a section on E times_V W to its restriction on the pulled-back triple.
3. Its further restriction to the target tube agrees with first restricting to the
source tube: both maps have the same two fibre-product projections. Pass to the
filtered stalk colimit. By the normalization in orientedPointCohomology, this is the
pointCohomology normalization, not an unspecified naturality assertion.
4. Apply the equality termwise to a K-injective representative. The derived comparison
to the pulled-back resolution and localization preserve that equality. In the present
sigma model it is also the counit-mate identity strictLocalDescription_ordinaryComparison,
followed by ordinary restriction and the Leray identity for sections. This proves the
displayed equality without assuming beta invertible or invoking truncated descent. -/
theorem ordinaryComparison [LocallyOfFiniteType f] [QuasiCompact f]
    {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g}
    (_H : IsPullback h f' f g) (d : Change z z' h g w)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ S]
    (K : EtaleDerived.{u, u + 1} X Λ)
    (_hKb : IsBounded (etaleDatum.{u, u + 1} X) (Coeff.{u, u + 1} Λ) K)
    (_hKc : ∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((Hypercover.readModules X Λ).obj
        ((DerivedCategory.homologyFunctor _ n).obj K))) :
    d.stalkRestriction Λ ((nearbyCycles f Λ).obj K) ≫
        (stalk z' Λ).map (baseChange f f' h g w Λ K) ≫
        pointCohomology z' Λ (((etaleModules.{u, u + 1} h).pull (Coeff Λ)).obj K) =
      pointCohomology z Λ K ≫ tubeRestriction d Λ K := by
  sorry

/-- Functoriality of the actual derived restriction maps, with all coefficient
identifications included. Applied to the augmented Cech nerve, this includes all
cofaces, degeneracies and augmentations, including their identity and composite cases.
Source: Orgogozo, Lemmas 2.6 and 2.6.1
(blueprint: lem-trf-finite-cover-tube-comparison).
Proof: expand restriction as the transpose of the pulled-back counit. Naturality moves
one comparison through the next unit, and the triangle identity cancels that unit and
counit. The normalized pullComposition identifies both coefficient composites with
the pullback along b followed by a. Both sides are therefore restriction along b then a. -/
theorem restrictionOver_comp {Y Z W : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ W)
    (r : W ⟶ X) (s : Z ⟶ X) (t : Y ⟶ X)
    (wb : b ≫ r = s) (wa : a ≫ s = t) (wab : (a ≫ b) ≫ r = t)
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived.{u, u + 1} X Λ) :
    restrictionOver b r s wb Λ K ≫ restrictionOver a s t wa Λ K =
      restrictionOver (a ≫ b) r t wab Λ K := by
  sorry

/-- The canonical strict-local base map, including transport to the chosen image point.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def Change.baseMap {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w) :=
  Scheme.strictHenselizationMap g (z'.x ≫ f') ≫
    eqToHom (congrArg Scheme.strictHenselizationScheme
      ((Category.assoc z'.x f' g).trans
        ((congrArg (fun k ↦ z'.x ≫ k) w.symm).trans
          ((Category.assoc z'.x h f).symm.trans
            (congrArg (fun k ↦ k ≫ f) d.x_over)))))

/-- The two base projections of the canonical tube map agree.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: use its second pullback projection and change.specialization. -/
theorem Change.toBase_comm {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w) :
    toBase z' ≫ d.baseMap = d.tubeMap ≫ toBase z := by
  sorry

/-- The chosen generizing geometric points commute with the local base map.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: the pointed equation in strictHenselizationMap_existsUnique for b' gives the
closed evaluation lift. Compose it with change.specialization and b_over. -/
theorem Change.basePoint_comm {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w) :
    basePoint z' ≫ d.baseMap = basePoint z := by
  sorry

/-- Q to U_0, for Q = U_0 times_(S_0) P. This is Q_q when p is the q-th Cech stage.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
abbrev changedCoverMap {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) :=
  pullback.fst d.baseMap p

/-- The map between the two covered tubes, given by their canonical projections.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def coverTubeMap {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) :
    coverTube z' (changedCoverMap d p) ⟶ coverTube z p :=
  pullback.map (toBase z') (changedCoverMap d p) (toBase z) p
    d.tubeMap (pullback.snd d.baseMap p) d.baseMap d.toBase_comm pullback.condition

/-- The covered-tube comparison is over the original source map h.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: use pullback.map_fst, change.tubeMap_over and reassociate. -/
theorem coverTubeMap_over {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) :
    coverTubeMap d p ≫ coverSource z p = coverSource z' (changedCoverMap d p) ≫ h := by
  sorry

/-- The actual column comparison A_q to B_q, with the coefficient-composition iso.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def coverRestriction {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived.{u, u + 1} X Λ) :
    coverSections z p Λ K ⟶ coverSections z' (changedCoverMap d p) Λ
      (((etaleModules.{u, u + 1} h).pull (Coeff Λ)).obj K) :=
  restrictionOver (coverTubeMap d p) (coverSource z p)
      (coverSource z' (changedCoverMap d p) ≫ h) (coverTubeMap_over d p) Λ K ≫
    (sections (coverTube z' (changedCoverMap d p)) Λ).map
      ((Hypercover.pullComposition h (coverSource z' (changedCoverMap d p)) Λ).inv.app K)

/-- Projection sends a geometric component lift of Q to the corresponding lift of P.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: the Q pullback equation, the defining equation of t, and basePoint_comm give
the equality after composition with p. -/
theorem componentProjection_over {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (t : Index z' (changedCoverMap d p)) :
    (t.val ≫ pullback.snd d.baseMap p) ≫ p = basePoint z := by
  sorry

/-- The projection-induced component map, written on their canonical geometric lifts.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def componentProjection {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) :
    Index z' (changedCoverMap d p) → Index z p :=
  fun t ↦ ⟨t.val ≫ pullback.snd d.baseMap p, componentProjection_over d p t⟩

/-- The cover projection lies over the original scheme base map g.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: strictHenselizationMap_over identifies the structural square of baseMap.
Compose its equation with the Q pullback condition. -/
theorem coverBase_comm {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) :
    (changedCoverMap d p ≫ Scheme.strictHenselizationStructuralMap (z'.x ≫ f')) ≫ g =
      pullback.snd d.baseMap p ≫
        (p ≫ Scheme.strictHenselizationStructuralMap (z.x ≫ f)) := by
  sorry

/-- The canonical horizontal map X_Q to X_P over Q to P.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def coverSchemeMap {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) :=
  pullback.map f' (changedCoverMap d p ≫ Scheme.strictHenselizationStructuralMap (z'.x ≫ f'))
    f (p ≫ Scheme.strictHenselizationStructuralMap (z.x ≫ f))
    h (pullback.snd d.baseMap p) g w.symm (coverBase_comm d p)

/-- The induced cover-family square commutes.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: this is pullback.map_snd for the constructed coverSchemeMap. -/
theorem coverSchemeMap_comm {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) :
    coverSchemeMap d p ≫ coverMorphism z p =
      coverMorphism z' (changedCoverMap d p) ≫ pullback.snd d.baseMap p := by
  sorry

/-- The induced cover-family square is Cartesian whenever the original square is.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: paste the defining pullback squares and the original Cartesian square, then
cancel their common outer pullback. The resulting map is coverSchemeMap by its projections. -/
theorem coverSchemeMap_isPullback {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    (H : IsPullback h f' f g)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) :
    IsPullback (coverSchemeMap d p) (coverMorphism z' (changedCoverMap d p))
      (coverMorphism z p) (pullback.snd d.baseMap p) := by
  sorry

/-- Compatibility of the two coefficient pullbacks from X.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: apply pullback.map_fst to coverSchemeMap; these are its defining source projections. -/
theorem coverSchemeMap_over {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) :
    coverSchemeMap d p ≫ pullback.fst f
        (p ≫ Scheme.strictHenselizationStructuralMap (z.x ≫ f)) =
      pullback.fst f'
        (changedCoverMap d p ≫ Scheme.strictHenselizationStructuralMap (z'.x ≫ f')) ≫ h := by
  sorry

/-- The canonical coefficient comparison between successive and direct pullback to X_Q.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def coverCoefficients {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived.{u, u + 1} X Λ) :=
  coefficientMap (coverSchemeMap d p) (pullback.fst _ _)
      (pullback.fst _ _ ≫ h) (coverSchemeMap_over d p) Λ K ≫
    (Hypercover.pullComposition h (pullback.fst _ _) Λ).inv.app K

/-- The derived section functor on one specified tube.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def tubeSectionFunctor (z : Point f Ω Ξ) (Λ : Type (u + 1)) [CommRing Λ] :=
  (etaleModules.{u, u + 1} (toSource z)).pull (Coeff Λ) ⋙ sections (tube z) Λ

/-- Compatible lifted points exist under the canonical Q to P projection. Different
components may still share their closed strictly local factor.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: the inverse image of an open-and-closed finite factor is open and closed. The
connected Q-factor containing the generic point meets it, hence maps into it. Its
closed point maps to the closed point because the local base map and the finite
strictly local factors have singleton closed fibres. Uniqueness of the geometric
lifts and of factorization through the open immersion gives the two point equations
and the specialization square. These are exactly Change's fields. -/
theorem liftedPoints_compatible {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) [IsFinite p]
    (l : ∀ t : Index z p, LiftedPoint z p t)
    (l' : ∀ t : Index z' (changedCoverMap d p), LiftedPoint z' (changedCoverMap d p) t) :
    Nonempty (∀ t : Index z' (changedCoverMap d p),
      Change (l (componentProjection d p t)).point (l' t).point
        (coverSchemeMap d p) (pullback.snd d.baseMap p) (coverSchemeMap_comm d p)) := by
  sorry

/-- The column comparison is componentwise restriction under the finite-product cones.
Together with ordinaryComparison for the displayed Cartesian cover square, these are
precisely the stalks of its ordinary nearby comparisons.
Source: Orgogozo, Lemma 2.6.1 (blueprint: lem-trf-finite-cover-tube-comparison).

Proof: under finiteTubeDecomposition, both component maps have the same projections
to the strict-local source factor and to P. Strict-local functoriality and uniqueness
in the fibre product make the square of component inclusions commute. Applying derived
sections and restrictionOver_comp gives the displayed equality, including the normalized
coefficient identifications. finiteSectionDecomposition says these cone maps are product
projections. Thus, if componentProjection is bijective, this is the product of component
maps, with the ordinary-comparison interpretation supplied by ordinaryComparison. -/
theorem coverRestriction_component {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) [IsFinite p]
    (l : ∀ t : Index z p, LiftedPoint z p t)
    (l' : ∀ t : Index z' (changedCoverMap d p), LiftedPoint z' (changedCoverMap d p) t)
    (t : Index z' (changedCoverMap d p))
    (D : Change (l (componentProjection d p t)).point (l' t).point
      (coverSchemeMap d p) (pullback.snd d.baseMap p) (coverSchemeMap_comm d p))
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived.{u, u + 1} X Λ) :
    coverRestriction d p Λ K ≫ (l' t).sectionRestriction Λ
        (((etaleModules.{u, u + 1} h).pull (Coeff Λ)).obj K) =
      (l (componentProjection d p t)).sectionRestriction Λ K ≫
        tubeRestriction D Λ
          (((etaleModules.{u, u + 1} (pullback.fst f
            (p ≫ Scheme.strictHenselizationStructuralMap (z.x ≫ f)))).pull (Coeff Λ)).obj K) ≫
        (tubeSectionFunctor (l' t).point Λ).map (coverCoefficients d p Λ K) := by
  sorry

/-- The canonical point-cohomology map remains invertible after coefficient pullback.
This auxiliary form supplies the isomorphism for each lifted finite-cover point.
Source: Illusie §1.3; Orgogozo, Lemma 2.6
(blueprint: lem-trf-finite-cover-tube-comparison).
Proof: étale inverse image is exact, so it preserves boundedness. Apply the normalized
bounded-below orientedPointCohomology theorem to the pulled-back complex. The section
and constant-module adjunctions in pointCohomology have the same terminal-section
normalization, so its map is the transported map of that theorem. -/
theorem pointCohomology_pullback_isIso {Y T : Scheme.{u}} {F : Y ⟶ T}
    (Z : Point F Ω Ξ) (a : Y ⟶ X) (Λ : Type (u + 1)) [CommRing Λ]
    (K : EtaleDerived.{u, u + 1} X Λ)
    (_hKb : IsBounded (etaleDatum.{u, u + 1} X) (Coeff.{u, u + 1} Λ) K) :
    IsIso (pointCohomology Z Λ (((etaleModules.{u, u + 1} a).pull (Coeff Λ)).obj K)) := by
  sorry

/-- The actual ordinary comparison stalk transported by the fixed point-cohomology
maps. Only the source point-cohomology map is inverted; beta is not inverted.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def ordinaryTubeMap {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived.{u, u + 1} X Λ)
    [IsIso (pointCohomology z Λ K)] :
    tubeSections z Λ K ⟶ tubeSections z' Λ
      (((etaleModules.{u, u + 1} h).pull (Coeff Λ)).obj K) :=
  inv (pointCohomology z Λ K) ≫ d.stalkRestriction Λ ((nearbyCycles f Λ).obj K) ≫
    (stalk z' Λ).map (baseChange f f' h g w Λ K) ≫
    pointCohomology z' Λ (((etaleModules.{u, u + 1} h).pull (Coeff Λ)).obj K)

/-- Under the bijection of component indices, every product coordinate of A to B is
exactly the corresponding ordinary-comparison stalk. The finite-product cones are
finiteSectionDecomposition; the right-hand map contains the actual baseChange arrow.
Source: Orgogozo, Lemmas 2.6 and 2.6.1
(blueprint: lem-trf-finite-cover-tube-comparison).
Proof: the cover-family square is Cartesian by coverSchemeMap_isPullback. The pullback
of the finite-type family is finite type; exact inverse image preserves boundedness
and preserves constructibility, and the invertible exponent pulls back. Apply
ordinaryComparison to D and cancel its source point-cohomology isomorphism. Substitute
this equality in coverRestriction_component. The hypothesis on the component projection
reindexes the two finite-product cones, giving the product asserted in the node. -/
theorem coverRestriction_ordinaryComparisons [LocallyOfFiniteType f] [QuasiCompact f]
    {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g}
    (_H : IsPullback h f' f g) (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) [IsFinite p]
    (_bij : Function.Bijective (componentProjection d p))
    (l : ∀ t : Index z p, LiftedPoint z p t)
    (l' : ∀ t : Index z' (changedCoverMap d p), LiftedPoint z' (changedCoverMap d p) t)
    (t : Index z' (changedCoverMap d p))
    (D : Change (l (componentProjection d p t)).point (l' t).point
      (coverSchemeMap d p) (pullback.snd d.baseMap p) (coverSchemeMap_comm d p))
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasInvertibleExponent Λ S]
    (K : EtaleDerived.{u, u + 1} X Λ)
    (hKb : IsBounded (etaleDatum.{u, u + 1} X) (Coeff.{u, u + 1} Λ) K)
    (_hKc : ∀ n : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((Hypercover.readModules X Λ).obj
        ((DerivedCategory.homologyFunctor _ n).obj K))) :
    letI := pointCohomology_pullback_isIso (l (componentProjection d p t)).point
      (pullback.fst f (p ≫ Scheme.strictHenselizationStructuralMap (z.x ≫ f))) Λ K hKb
    coverRestriction d p Λ K ≫ (l' t).sectionRestriction Λ
        (((etaleModules.{u, u + 1} h).pull (Coeff Λ)).obj K) =
      (l (componentProjection d p t)).sectionRestriction Λ K ≫
        ordinaryTubeMap D Λ
          (((etaleModules.{u, u + 1} (pullback.fst f
            (p ≫ Scheme.strictHenselizationStructuralMap (z.x ≫ f)))).pull (Coeff Λ)).obj K) ≫
        (tubeSectionFunctor (l' t).point Λ).map (coverCoefficients d p Λ K) := by
  sorry

/-- The actual q-th map P_q to S_0 of Mathlib's augmented Cech nerve, with q+1 factors.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
abbrev cechMap (z : Point f Ω Ξ) {P : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f)) (q : ℕ) :=
  (Arrow.mk p).augmentedCechNerve.hom.app (op (SimplexCategory.mk q))

/-- Every Cech stage of a finite surjective cover is finite surjective.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: the wide fibre product with q+1 entries is obtained by repeated base changes
and compositions of p. These preserve finiteness and surjectivity; q=0 has one entry. -/
theorem cechMap_finite_surjective (z : Point f Ω Ξ) {P : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    [IsFinite p] [Surjective p] (q : ℕ) :
    IsFinite (cechMap z p q) ∧ Surjective (cechMap z p q) := by
  sorry

/-- The over-base equation that defines transition maps between covered tubes.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: compose the source pullback equation with w, then reassociate. -/
theorem coverTransition_condition (z : Point f Ω Ξ) {P R : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (r : R ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (a : R ⟶ P) (w : a ≫ p = r) :
    pullback.fst (toBase z) r ≫ toBase z =
      (pullback.snd (toBase z) r ≫ a) ≫ p := by
  sorry

/-- Transition between covered tubes, including every face and degeneracy of P's nerve.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def coverTransition (z : Point f Ω Ξ) {P R : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (r : R ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (a : R ⟶ P) (w : a ≫ p = r) : coverTube z r ⟶ coverTube z p :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a)
    (coverTransition_condition z p r a w)

/-- A transition between covers is over X.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: its first projection is the first projection of its source, by pullback.lift_fst. -/
theorem coverTransition_over (z : Point f Ω Ξ) {P R : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (r : R ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (a : R ⟶ P) (w : a ≫ p = r) :
    coverTransition z p r a w ≫ coverSource z p = coverSource z r := by
  sorry

/-- The restriction on A's augmented Cech diagram, for any map over S_0.
Specializing a to the nerve map of any simplex morphism gives all its structure maps.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def coverCoface (z : Point f Ω Ξ) {P R : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (r : R ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (a : R ⟶ P) (w : a ≫ p = r)
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived.{u, u + 1} X Λ) :=
  restrictionOver (coverTransition z p r a w) (coverSource z p) (coverSource z r)
    (coverTransition_over z p r a w) Λ K

/-- The induced Q_r to Q_p map is over U_0.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: this is pullback.lift_fst for the pullback of a over baseMap. -/
theorem changedTransition_over {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P R : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (r : R ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (a : R ⟶ P) (wa : a ≫ p = r) :
    pullback.map d.baseMap r d.baseMap p (𝟙 _) a (𝟙 _)
        (by simp) (by simpa using wa.symm) ≫ changedCoverMap d p = changedCoverMap d r := by
  sorry

/-- Every coface and degeneracy commutes with the actual column restriction A to B.
This is quantified over all maps of covers, so in particular over all simplex maps
of the actual augmented Cech nerve, with no truncation or descent hypothesis.
Source: Orgogozo, Lemmas 2.6 and 2.6.1
(blueprint: lem-trf-finite-cover-tube-comparison).
Proof: both composites of geometric tube maps have the same projection to tube z
and to P, by pullback.map_fst and pullback.map_snd. The pullback universal property
makes them equal. Apply restrictionOver_comp, including the normalized coefficient
composition. After the finite-product cone identifications this remains the same
equality coordinate by coordinate, proving compatibility of the product description. -/
theorem coverRestriction_coface {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P R : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (r : R ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (a : R ⟶ P) (wa : a ≫ p = r)
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived.{u, u + 1} X Λ) :
    coverCoface z p r a wa Λ K ≫ coverRestriction d r Λ K =
      coverRestriction d p Λ K ≫
        coverCoface z' (changedCoverMap d p) (changedCoverMap d r)
          (pullback.map d.baseMap r d.baseMap p (𝟙 _) a (𝟙 _)
            (by simp) (by simpa using wa.symm)) (changedTransition_over d p r a wa) Λ
          (((etaleModules.{u, u + 1} h).pull (Coeff Λ)).obj K) := by
  sorry

/-- The augmentation from the original tube sections to the q-th covered sections.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison). -/
def coverAugmentation (z : Point f Ω Ξ) {P : Scheme.{u}}
    (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived.{u, u + 1} X Λ) :
    tubeSections z Λ K ⟶ coverSections z p Λ K :=
  restrictionOver (pullback.fst (toBase z) p) (toSource z) (coverSource z p) rfl Λ K

/-- The actual column restrictions commute with the augmentations from M and N.
Source: Orgogozo, Lemma 2.6 (blueprint: lem-trf-finite-cover-tube-comparison).
Proof: the square of the canonical covered-tube projections commutes by
pullback.map_fst. Apply restrictionOver_comp and normalized pullback composition;
both sides restrict along that same map to the covered target tube. -/
theorem coverRestriction_augmentation {z : Point f Ω Ξ} {z' : Point f' Ω Ξ}
    {h : X' ⟶ X} {g : S' ⟶ S} {w : h ≫ f = f' ≫ g} (d : Change z z' h g w)
    {P : Scheme.{u}} (p : P ⟶ Scheme.strictHenselizationScheme (z.x ≫ f))
    (Λ : Type (u + 1)) [CommRing Λ] (K : EtaleDerived.{u, u + 1} X Λ) :
    coverAugmentation z p Λ K ≫ coverRestriction d p Λ K =
      tubeRestriction d Λ K ≫ coverAugmentation z' (changedCoverMap d p) Λ
        (((etaleModules.{u, u + 1} h).pull (Coeff Λ)).obj K) := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles.FiniteCoverTubeComparison
