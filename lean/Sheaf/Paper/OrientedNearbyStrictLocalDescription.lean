/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.Paper.OrientedProductPointsConservative
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Sheaf.CategoryTheory.Sites.LocalOrientedProjectionExact
import Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.TraceFormula.OrientedPointCohomology
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.IndEtaleAffineStrictLocalBaseChange
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations
public import Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula
import Sheaf.Paper.StrictHenselizationFunctoriality

/-!
# Strict-local sections and the localized base-change test for nearby cycles

Source: Zheng, Appendix A, Remark A.2, (A.2.1), and proof of Theorem A.3, (A.3.1);
Illusie, Around the Thom--Sebastiani theorem, (1.11.1)--(1.12.6)
(blueprint: lem-trf-oriented-nearby-strict-local-description).

## Main definitions

* `strictLocalSigma`: the section with its closed-point counit orientation.
* `strictLocalDescriptionComparison`: the specified natural description map.
* `strictLocalDirectBaseChange`: the ordinary pulled-back-counit mate.
* `StrictLocalTestSquare` and `HasLocalizedBaseChange`: the localized test.

## Main statements

* `strictLocalDescriptionComparison_isIso`: the unbounded description.
* `strictLocalSigma_jointly_conservative`: conservativity on derived morphisms.
* `strictLocalDescription_ordinaryComparison`, `strictLocalDescription_laxTensor`,
  `strictLocalDescription_externalProduct`: compatibility with the specified maps.
* `strictLocalDescription_baseChangeCriterion`: the criterion and its stability.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v s

open CategoryTheory CategoryTheory.Limits CategoryTheory.AdicSites Opposite

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- Global sections in the transported étale presentation.
Source: Illusie (1.11.3) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def localSections (X : Scheme.{u}) :
    Sheaf (etaleTopology.{u, v} X) (Type (max (u + 1) v)) ⥤ Type (max (u + 1) v) :=
  (etaleSheafEquivalence X).inverse ⋙
    (sheafSections X.smallEtaleTopology (Type (max (u + 1) v))).obj
      (op (⊤_ X.Etale))

/-- The geometric morphism to sets, through the explicit site equivalence.
Source: Illusie (1.11.3) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def localEpsilon (X : Scheme.{u}) :
    GeometricMorphism (Sheaf (etaleTopology.{u, v} X) (Type (max (u + 1) v)))
      (Type (max (u + 1) v)) where
  inverse := constantSheaf X.smallEtaleTopology (Type (max (u + 1) v)) ⋙
    (etaleSheafEquivalence X).functor
  direct := localSections.{u, v} X
  adj := (constantSheafAdj X.smallEtaleTopology (Type (max (u + 1) v))
    terminalIsTerminal).comp (etaleSheafEquivalence X).toAdjunction
  leftExact := by unfold constantSheaf; infer_instance

/-- The geometric stalk/skyscraper adjunction, with the punctual presentation removed.
Source: Illusie §1.11; Stacks 04HU
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def localPoint {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    GeometricMorphism (Type (max (u + 1) v))
      (Sheaf (etaleTopology.{u, v} X) (Type (max (u + 1) v))) where
  inverse := (etaleSheafEquivalence X).inverse ⋙ (Scheme.pointSmallEtale x).sheafFiber
  direct := (Scheme.pointSmallEtale x).skyscraperSheafFunctor ⋙
    (etaleSheafEquivalence X).functor
  adj := (etaleSheafEquivalence X).symm.toAdjunction.comp
    (Scheme.pointSmallEtale x).skyscraperSheafAdjunction
  leftExact := by
    let : AB5OfSize.{u, u} (Type (max (u + 1) v)) :=
      AB5OfSize_of_univLE.{u, u, max (u + 1) v, max (u + 1) v} _
    infer_instance

/-- Restriction from global sections to the specified geometric stalk.
Source: Illusie (1.11.3) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def localGerm {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) : localSections.{u, v} X ⟶ (localPoint.{u, v} x).inverse where
  app H := (Scheme.pointSmallEtale x).toPresheafFiber (⊤_ X.Etale)
    ((Scheme.pointSmallEtale x).fiber.map (terminal.from (Scheme.Etale.mk (𝟙 X)))
      (Over.homMk x (by simp))) ((etaleSheafEquivalence X).inverse.obj H).obj
  naturality H K a :=
    ((Scheme.pointSmallEtale x).toPresheafFiber_naturality
      ((etaleSheafEquivalence X).inverse.map a).hom _ _).symm

/-- The direct-image global-section identity is fixed by the unique final-object map.
Source: Illusie (1.11.3) (blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: base change preserves the final étale object. The unique isomorphism of final
objects gives these components; presheaf naturality gives a natural iso. The displayed
formula specifies every component, so the iso is unique. -/
theorem localDirectSections_existsUnique {A B : Scheme.{u}} (a : A ⟶ B) :
    ∃! e : (etaleMorphism.{u, v} a).direct ⋙ localSections.{u, v} B ≅ localSections.{u, v} A,
      ∀ H : Sheaf (etaleTopology.{u, v} A) (Type (max (u + 1) v)),
        e.hom.app H = H.obj.map
          ((((terminalIsTerminal.isTerminalObj
            (AsSmall.equiv : B.Etale ≌ EtaleSite.{u, v} B).functor
            (⊤_ B.Etale)).isTerminalObj (etaleBaseChange a) _).uniqueUpToIso
              (terminalIsTerminal.isTerminalObj
                (AsSmall.equiv : A.Etale ≌ EtaleSite.{u, v} A).functor
                (⊤_ A.Etale))).inv.op) := by
  sorry

/-- Global sections after direct image, with the preceding component normalization.
Source: Illusie (1.11.3) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def localDirectSections {A B : Scheme.{u}} (a : A ⟶ B) :=
  (localDirectSections_existsUnique.{u, v} a).choose

/-- The actual global-section germ at the image of the closed point.
Source: Illusie (1.11.3) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalImageGerm {A B : Scheme.{u}} (a : A ⟶ B)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ A) :
    localSections.{u, v} B ⟶ ((localPoint.{u, v} x).comp (etaleMorphism a)).inverse :=
  Functor.whiskerRight (etaleMorphism a).adj.unit (localSections.{u, v} B) ≫
    Functor.whiskerLeft (etaleMorphism a).inverse (localDirectSections.{u, v} a).hom ≫
    Functor.whiskerLeft (etaleMorphism a).inverse (localGerm.{u, v} x)

/-- The canonical geometric lift to the strict localization.
Source: Illusie §1.11; Stacks 04GU
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
abbrev strictLocalPoint {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :=
  Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation x))

/-- The normalized germ is invertible for the local map between strict localizations.
Source: Illusie (1.11.3); ILO XI 2.2
(blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: the source and target are strictly local and the functorial map sends the
canonical closed point to the canonical closed point. Global sections on the target
are its closed-point stalk. The stalk of inverse image is the source-point stalk;
these identifications send the displayed map to the identity on the target stalk. -/
theorem strictLocalImageGerm_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    IsIso (strictLocalImageGerm.{u, v} (Scheme.strictHenselizationMap f x)
      (strictLocalPoint x)) := by
  sorry

/-- The germ isomorphism, with no choice of a specialization automorphism.
Source: Illusie (1.11.3) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalGermIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :=
  letI := strictLocalImageGerm_isIso.{u, v} f x
  asIso (strictLocalImageGerm.{u, v} (Scheme.strictHenselizationMap f x) (strictLocalPoint x))

/-- The closed-point counit, expressed in the direct-image convention for 2-morphisms.
Source: Illusie (1.11.3) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalOrientation {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ((identity _).comp (identity _)).direct ⟶
      (((localEpsilon.{u, v} (Scheme.strictHenselizationScheme (x ≫ f))).comp
        (localPoint.{u, v} (strictLocalPoint x))).comp
          (etaleMorphism.{u, v} (Scheme.strictHenselizationMap f x))).direct :=
  (Functor.leftUnitor _).hom ≫
    (conjugateEquiv (identity _).adj
      ((((localEpsilon.{u, v} (Scheme.strictHenselizationScheme (x ≫ f))).comp
        (localPoint.{u, v} (strictLocalPoint x))).comp
          (etaleMorphism (Scheme.strictHenselizationMap f x))).adj))
      (Functor.whiskerRight (strictLocalGermIso.{u, v} f x).inv
        (localEpsilon.{u, v} (Scheme.strictHenselizationScheme (x ≫ f))).inverse ≫
          (localEpsilon.{u, v} (Scheme.strictHenselizationScheme (x ≫ f))).adj.counit)

/-- The universal lift with the specified closed-point counit orientation.
Source: Illusie (1.11.2)--(1.11.4)
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalLift {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :=
  lift.{u, v} (Scheme.strictHenselizationMap f x) _ (sheaf_isTopos _)
    ((localEpsilon.{u, v} (Scheme.strictHenselizationScheme (x ≫ f))).comp
      (localPoint.{u, v} (strictLocalPoint x))) (identity _) (strictLocalOrientation.{u, v} f x)

/-- The induced map from the localized vanishing topos to the original one.
Source: Illusie (1.11.5) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalVanishing {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :=
  squareMorphism.{u, v} f (Scheme.strictHenselizationMap f x)
    (Scheme.strictHenselizationStructuralMap x)
    (Scheme.strictHenselizationStructuralMap (x ≫ f))
    (Scheme.strictHenselizationMap_over f x).symm

/-- The canonical section σ_x, composed with the localization map of vanishing topoi.
Its orientation is the normalized closed-point counit, not a separately chosen map.
Source: Illusie (1.11.5) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalSigma {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :=
  (strictLocalLift.{u, v} f x).morphism.comp (strictLocalVanishing.{u, v} f x)

/-- Constant-coefficient modules for the specified strict-local section.
Source: Illusie (1.11.6) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalSigmaModules {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :=
  moduleMorphism (vanishingDatum.{u, v} f)
    (etaleDatum.{u, v} (Scheme.strictHenselizationScheme (x ≫ f))) (strictLocalSigma.{u, v} f x)

/-- The exact module lift of the identity is uniquely normalized by scalar insertion.
Source: Stacks 03D2; Illusie §1.11
(blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: multiplication identifies extension along the canonical identity-ring map with
the original module. It sends 1 tensor m to m; these generators give uniqueness. -/
theorem strictLocalModuleIdentity_existsUnique (S : Site.{s}) (A : Type s) [CommRing A] :
    ∃! e : (moduleMorphism S S (identity _)).modulePull A ≅ 𝟭 (S.modules A),
      ∀ M : S.modules A,
        ConstantCompletion.pullInsertion (moduleMorphism S S (identity _)).algebra
          (ConstantCompletion.constantMap (moduleMorphism S S (identity _)).algebra A) M ≫
          (ConstantCompletion.underlying (S.ring A)).map (e.hom.app M) = 𝟙 _ := by
  sorry

/-- Localization of the scalar-insertion-normalized identity comparison.
Source: Stacks 03D2 (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalIdentityPull (S : Site.{s}) (A : Type s) [CommRing A] :
    (moduleMorphism S S (identity _)).pull A ≅ 𝟭 (S.derived A) :=
  Functor.mapDerivedCategoryNatIso (strictLocalModuleIdentity_existsUnique S A).choose ≪≫
    Functor.mapDerivedCategoryIdIso (S.modules A)

/-- Exact module pullback of a composite, with its canonical scalar-insertion comparison.
Source: Stacks 03D2; Illusie §1.11
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalPullComp {S T U : Site.{s}}
    (a : GeometricMorphism (Sheaf U.topology (Type s)) (Sheaf T.topology (Type s)))
    (b : GeometricMorphism (Sheaf T.topology (Type s)) (Sheaf S.topology (Type s)))
    (A : Type s) [CommRing A] :
    (moduleMorphism S T b).pull A ⋙ (moduleMorphism T U a).pull A ≅
      (moduleMorphism S U (a.comp b)).pull A :=
  derivedSquare (f := moduleMorphism S U (a.comp b)) (g := moduleMorphism S T b)
    (h := moduleMorphism U U (identity _)) (k := moduleMorphism T U a)
    (Functor.rightUnitor _).symm A ≪≫
      Functor.isoWhiskerLeft _ (strictLocalIdentityPull U A) ≪≫ Functor.rightUnitor _

/-- An isomorphism of geometric inverse images induces the specified derived module iso.
Source: Stacks 03D2 (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalPullIso {S T : Site.{s}}
    (a b : GeometricMorphism (Sheaf T.topology (Type s)) (Sheaf S.topology (Type s)))
    (e : a.inverse ≅ b.inverse) (A : Type s) [CommRing A] :
    (moduleMorphism S T a).pull A ≅ (moduleMorphism S T b).pull A :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (strictLocalIdentityPull T A).symm ≪≫
    derivedSquare (f := moduleMorphism S T b) (g := moduleMorphism S T a)
      (h := moduleMorphism T T (identity _)) (k := moduleMorphism T T (identity _))
      (Functor.isoWhiskerRight e (𝟭 _)) A ≪≫
    Functor.isoWhiskerLeft _ (strictLocalIdentityPull T A) ≪≫ Functor.rightUnitor _

/-- The localized section as a morphism of constant-coefficient module sites.
Source: Illusie (1.11.2) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalSectionModules {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :=
  moduleMorphism (vanishingDatum.{u, v} (Scheme.strictHenselizationMap f x))
    (etaleDatum.{u, v} (Scheme.strictHenselizationScheme (x ≫ f))) (strictLocalLift.{u, v} f
      x).morphism

/-- The second projection of the localized vanishing topos on modules.
Source: Illusie (1.11.4) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalSecondModules {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :=
  moduleMorphism (etaleDatum.{u, v} (Scheme.strictHenselizationScheme (x ≫ f)))
    (vanishingDatum.{u, v} (Scheme.strictHenselizationMap f x))
    (p₂.{u, v} (Scheme.strictHenselizationMap f x))

/-- The normalized identity p₂σ = 1 on derived inverse images.
Source: Illusie (1.11.4) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalSectionPull {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (Λ : Type v) [CommRing Λ] :
    (strictLocalSecondModules.{u, v} f x).pull (Coeff.{u, v} Λ) ⋙
        (strictLocalSectionModules.{u, v} f x).pull (Coeff.{u, v} Λ) ≅
      𝟭 (EtaleDerived (Scheme.strictHenselizationScheme (x ≫ f)) Λ) :=
  strictLocalPullComp
    (S := etaleDatum.{u, v} (Scheme.strictHenselizationScheme (x ≫ f)))
    (T := vanishingDatum.{u, v} (Scheme.strictHenselizationMap f x))
    (U := etaleDatum.{u, v} (Scheme.strictHenselizationScheme (x ≫ f)))
    (strictLocalLift.{u, v} f x).morphism
    (p₂.{u, v} (Scheme.strictHenselizationMap f x)) (Coeff.{u, v} Λ) ≪≫
    strictLocalPullIso
      (S := etaleDatum.{u, v} (Scheme.strictHenselizationScheme (x ≫ f)))
      (T := etaleDatum.{u, v} (Scheme.strictHenselizationScheme (x ≫ f)))
      ((strictLocalLift.{u, v} f x).morphism.comp (p₂.{u, v} (Scheme.strictHenselizationMap f x)))
      (identity _) (GeometricMorphism.inverseIso (strictLocalLift.{u, v} f x).second).symm
      (Coeff.{u, v} Λ) ≪≫
    strictLocalIdentityPull _ (Coeff.{u, v} Λ)

/-- The local-projection comparison is the adjunction mate of the inverse section identity.
Source: ILO XI 2.3; Illusie (1.12.1)
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalProjectionComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (Λ : Type v) [CommRing Λ] :
    (strictLocalSecondModules.{u, v} f x).push (Coeff.{u, v} Λ) ⟶
      (strictLocalSectionModules.{u, v} f x).pull (Coeff.{u, v} Λ) :=
  (Functor.rightUnitor _).inv ≫
    ((((strictLocalSecondModules.{u, v} f x).adj (Coeff.{u, v} Λ)).whiskerLeft
      (EtaleDerived (Scheme.strictHenselizationScheme (x ≫ f)) Λ)).homEquiv
        (𝟭 _) ((strictLocalSectionModules.{u, v} f x).pull (Coeff.{u, v} Λ))).symm
        (strictLocalSectionPull.{u, v} f x Λ).inv

/-- Gabber's local-projection lemma makes this particular unit comparison invertible.
Source: ILO XI Proposition 2.3, Corollary 2.3.1; Illusie (1.12.1)
(blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: apply lem-trf-local-oriented-projection-exact to the pointed local morphism
between strict localizations. Transport its module lifts to the AsSmall sites using
scalar insertions. The defining adjunct above is its unit comparison. That direct
image is exact, so the underived isomorphism applies termwise to every complex and
descends through the quasi-isomorphism localization, including unbounded complexes. -/
theorem strictLocalProjectionComparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (Λ : Type v) [CommRing Λ] : IsIso (strictLocalProjectionComparison.{u, v} f x Λ) := by
  sorry

/-- The exact local-projection isomorphism, retaining the specified unit comparison.
Source: Illusie (1.12.1) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalProjectionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (Λ : Type v) [CommRing Λ] :
    (strictLocalSecondModules.{u, v} f x).push (Coeff.{u, v} Λ) ≅
      (strictLocalSectionModules.{u, v} f x).pull (Coeff.{u, v} Λ) :=
  letI := strictLocalProjectionComparison_isIso.{u, v} f x Λ
  asIso (strictLocalProjectionComparison.{u, v} f x Λ)

/-- The specified identity p₂ψ = g on derived inverse images.
Source: Illusie §1.12 (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalPsiSecondPull {A B : Scheme.{u}} (g : A ⟶ B)
    (Λ : Type v) [CommRing Λ] :
    (moduleMorphism (etaleDatum.{u, v} B) (vanishingDatum.{u, v} g) (p₂.{u, v} g)).pull
      (Coeff.{u, v} Λ) ⋙
        (psiModules.{u, v} g).pull (Coeff.{u, v} Λ) ≅ (etaleModules.{u, v} g).pull (Coeff.{u, v}
          Λ) :=
  strictLocalPullComp (S := etaleDatum.{u, v} B) (T := vanishingDatum.{u, v} g)
    (U := etaleDatum.{u, v} A) (psi.{u, v} g) (p₂.{u, v} g) (Coeff.{u, v} Λ) ≪≫
    strictLocalPullIso (S := etaleDatum.{u, v} B) (T := etaleDatum.{u, v} A)
      ((psi.{u, v} g).comp (p₂.{u, v} g)) (etaleMorphism.{u, v} g)
      (GeometricMorphism.inverseIso (psiLift.{u, v} g).second).symm (Coeff.{u, v} Λ)

/-- Right adjoint uniqueness, with the fixed inverse-image identity p₂ψ = g.
Source: Illusie §1.12 (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalPsiSecondPush {A B : Scheme.{u}} (g : A ⟶ B)
    (Λ : Type v) [CommRing Λ] :
    nearbyCycles.{u, v} g Λ ⋙
        (moduleMorphism (etaleDatum.{u, v} B) (vanishingDatum.{u, v} g) (p₂.{u, v} g)).push
          (Coeff.{u, v} Λ) ≅
      (etaleModules.{u, v} g).push (Coeff.{u, v} Λ) :=
  ((((moduleMorphism (etaleDatum.{u, v} B) (vanishingDatum.{u, v} g) (p₂.{u, v} g)).adj
    (Coeff.{u, v} Λ)).comp
    ((psiModules.{u, v} g).adj (Coeff.{u, v} Λ))).ofNatIsoLeft
      (strictLocalPsiSecondPull.{u, v} g Λ)).rightAdjointUniq ((etaleModules.{u, v} g).adj
        (Coeff.{u, v}
        Λ))

/-- The ordinary nearby-cycle comparison as a natural transformation, using its fixed mate.
Source: Illusie §1.9 (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalNearbyComparison {T' B' T B : Scheme.{u}} (f : T ⟶ B) (f' : T' ⟶ B')
    (h : T' ⟶ T) (k : B' ⟶ B) (comm : h ≫ f = f' ≫ k)
    (Λ : Type v) [CommRing Λ] :
    nearbyCycles.{u, v} f Λ ⋙ (squareModules f f' h k comm).pull (Coeff.{u, v} Λ) ⟶
      (etaleModules.{u, v} h).pull (Coeff.{u, v} Λ) ⋙ nearbyCycles.{u, v} f' Λ :=
  (mateEquiv ((psiModules.{u, v} f).adj (Coeff.{u, v} Λ)) ((psiModules.{u, v} f').adj (Coeff.{u,
    v} Λ))
    (TwoSquare.mk _ _ _ _ (nearbySquare f f' h k comm Λ).hom)).natTrans

/-- The canonical map in the strict-local description, before asserting invertibility.
It is the ordinary comparison followed by the inverse unit comparison and the
right-adjoint identification p₂,* Rψ_* = Rg_*.
Source: Illusie (1.12.4)--(1.12.6); Zheng (A.2.1)
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalDescriptionComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (Λ : Type v) [CommRing Λ] :
    nearbyCycles.{u, v} f Λ ⋙ (strictLocalSigmaModules.{u, v} f x).pull (Coeff.{u, v} Λ) ⟶
      (etaleModules.{u, v} (Scheme.strictHenselizationStructuralMap x)).pull (Coeff.{u, v} Λ) ⋙
        (etaleModules.{u, v} (Scheme.strictHenselizationMap f x)).push (Coeff.{u, v} Λ) :=
  let n := nearbyCycles.{u, v} f Λ
  let g := Scheme.strictHenselizationMap f x
  let j := Scheme.strictHenselizationStructuralMap x
  let k := Scheme.strictHenselizationStructuralMap (x ≫ f)
  let c := (Scheme.strictHenselizationMap_over f x).symm
  let vPull := (squareModules.{u, v} f g j k c).pull (Coeff.{u, v} Λ)
  let sPull := (strictLocalSectionModules.{u, v} f x).pull (Coeff.{u, v} Λ)
  let jPull := (etaleModules.{u, v} j).pull (Coeff.{u, v} Λ)
  let ng := nearbyCycles.{u, v} g Λ
  (Functor.isoWhiskerLeft n
    (strictLocalPullComp (S := vanishingDatum.{u, v} f)
      (T := vanishingDatum.{u, v} g)
      (U := etaleDatum.{u, v} (Scheme.strictHenselizationScheme (x ≫ f)))
      (strictLocalLift.{u, v} f x).morphism (strictLocalVanishing.{u, v} f x)
      (Coeff.{u, v} Λ)).symm).hom ≫
    (Functor.associator n vPull sPull).inv ≫
    Functor.whiskerRight (strictLocalNearbyComparison.{u, v} f g j k c Λ) sPull ≫
    (Functor.associator jPull ng sPull).hom ≫
    (Functor.isoWhiskerLeft jPull
      (Functor.isoWhiskerLeft ng (strictLocalProjectionIso.{u, v} f x Λ).symm)).hom ≫
    (Functor.isoWhiskerLeft jPull (strictLocalPsiSecondPush.{u, v} g Λ)).hom

/-- The unbounded strict-local description for torsion coefficients and locally finite type f.
Source: Zheng Remark A.2, (A.2.1); Illusie (1.12.6)
(blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: first take a bounded-below complex. Oriented-point cohomology and the torsion
strict-local stalk formula identify both sides with the same Milnor-tube cohomology.
The coefficient-forgetting comparison justifies using the abelian stalk formula;
ind-étale invariance identifies the iterated base localization. These identifications
carry the displayed map to restriction from the same pointed neighbourhoods, so it
is invertible by geometric-stalk conservativity. For an arbitrary complex choose a
K-injective resolution with injective terms. The bounded-below assertion applied to
one injective sheaf shows that its restriction is g_*-acyclic. The universal torsion
finite-type (*) bound supplies finite cohomological dimension for g at this x.
The finite-cd acyclic-complex theorem therefore computes Rg_* on the restricted
resolution. The degree-zero isomorphism applies termwise, proving the assertion
without requiring the restricted resolution to be K-injective. -/
theorem strictLocalDescriptionComparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (Λ : Type v) [CommRing Λ]
    (m : ℕ) (hm : 1 ≤ m) (hΛ : ∀ a : Λ, (m : Λ) * a = 0)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    IsIso (strictLocalDescriptionComparison.{u, v} f x Λ) := by
  sorry

/-- The ordinary strict-local direct-image square, before taking its right-adjoint mate.
Source: Zheng Remark A.2(1); Stacks 03Q1
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalDirectSquare {A B A' B' : Scheme.{u}} (g : A ⟶ B) (g' : A' ⟶ B')
    (h : A' ⟶ A) (k : B' ⟶ B) (comm : h ≫ g = g' ≫ k)
    (Λ : Type v) [CommRing Λ] :
    (etaleModules.{u, v} k).pull (Coeff.{u, v} Λ) ⋙ (etaleModules.{u, v} g').pull (Coeff.{u, v} Λ) ≅
      (etaleModules.{u, v} g).pull (Coeff.{u, v} Λ) ⋙ (etaleModules.{u, v} h).pull (Coeff.{u, v}
        Λ) :=
  derivedSquare (f := etaleModules.{u, v} g) (g := etaleModules.{u, v} k)
    (h := etaleModules.{u, v} h) (k := etaleModules.{u, v} g')
    (GeometricMorphism.inverseIso (squareDirect g g' h k comm)) (Coeff.{u, v} Λ)

/-- The ordinary comparison is precisely the transpose of the pulled-back counit.
Source: Zheng Remark A.2(1), displayed local square
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalDirectBaseChange {A B A' B' : Scheme.{u}} (g : A ⟶ B) (g' : A' ⟶ B')
    (h : A' ⟶ A) (k : B' ⟶ B) (comm : h ≫ g = g' ≫ k)
    (Λ : Type v) [CommRing Λ] (K : EtaleDerived A Λ) :
    ((etaleModules.{u, v} k).pull (Coeff.{u, v} Λ)).obj
        (((etaleModules.{u, v} g).push (Coeff.{u, v} Λ)).obj K) ⟶
      ((etaleModules.{u, v} g').push (Coeff.{u, v} Λ)).obj
        (((etaleModules.{u, v} h).pull (Coeff.{u, v} Λ)).obj K) :=
  ((etaleModules.{u, v} g').adj (Coeff.{u, v} Λ)).homEquiv _ _
    ((strictLocalDirectSquare.{u, v} g g' h k comm Λ).hom.app
        (((etaleModules.{u, v} g).push (Coeff.{u, v} Λ)).obj K) ≫
      ((etaleModules.{u, v} h).pull (Coeff.{u, v} Λ)).map
        (((etaleModules.{u, v} g).adj (Coeff.{u, v} Λ)).counit.app K))

/-- Being a strict-localization morphism means being the structural map, up to an iso
of the source, at an actual geometric point of the target.
Source: Zheng Remark A.2(1)
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
structure StrictLocalLocalization {A B : Scheme.{u}} (a : A ⟶ B) where
  field : Type u
  [fieldStructure : Field field]
  [algebraicallyClosed : IsAlgClosed field]
  point : Spec (.of field) ⟶ B
  iso : A ≅ Scheme.strictHenselizationScheme point
  over : iso.hom ≫ Scheme.strictHenselizationStructuralMap point = a

/-- A local essentially Cartesian square, including the strict-localization property
of its induced map to the fibre product. Ring presentations merely express that all
four schemes are strictly local and that all three arrows preserve their closed points.
Source: Zheng Remark A.2(1)
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
structure StrictLocalTestSquare {A B : Scheme.{u}} (g : A ⟶ B) where
  source : Scheme.{u}
  target : Scheme.{u}
  h : source ⟶ A
  k : target ⟶ B
  g' : source ⟶ target
  comm : h ≫ g = g' ≫ k
  sourceRing : CommRingCat.{u}
  targetRing : CommRingCat.{u}
  sourceRing' : CommRingCat.{u}
  targetRing' : CommRingCat.{u}
  [sourceStrict : IsStrictlyHenselianLocalRing sourceRing]
  [targetStrict : IsStrictlyHenselianLocalRing targetRing]
  [sourceStrict' : IsStrictlyHenselianLocalRing sourceRing']
  [targetStrict' : IsStrictlyHenselianLocalRing targetRing']
  eA : A ≅ Spec sourceRing
  eB : B ≅ Spec targetRing
  eA' : source ≅ Spec sourceRing'
  eB' : target ≅ Spec targetRing'
  local_g : (eA.inv ≫ g ≫ eB.hom) (IsLocalRing.closedPoint sourceRing) =
    IsLocalRing.closedPoint targetRing
  local_h : (eA'.inv ≫ h ≫ eA.hom) (IsLocalRing.closedPoint sourceRing') =
    IsLocalRing.closedPoint sourceRing
  local_k : (eB'.inv ≫ k ≫ eB.hom) (IsLocalRing.closedPoint targetRing') =
    IsLocalRing.closedPoint targetRing
  local_g' : (eA'.inv ≫ g' ≫ eB'.hom) (IsLocalRing.closedPoint sourceRing') =
    IsLocalRing.closedPoint targetRing'
  essentiallyCartesian : Nonempty (StrictLocalLocalization (pullback.lift h g' comm))

/-- Localized base-change invariance tests all local essentially Cartesian squares.
The inverse image is exact, and the tested map is the specified counit mate.
Source: Zheng Remark A.2(1)
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def HasLocalizedBaseChange {A B : Scheme.{u}} (g : A ⟶ B)
    (Λ : Type v) [CommRing Λ] (K : EtaleDerived A Λ) : Prop :=
  ∀ S : StrictLocalTestSquare g,
    IsIso (strictLocalDirectBaseChange.{u, v} g S.g' S.h S.k S.comm Λ K)

/-- The ordinary lax tensor map for a direct image is the tensor-of-counits mate.
Source: Zheng (A.3.1); def-kun-projection-formula-map
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalDirectLax {A B : Scheme.{u}} (g : A ⟶ B)
    (Λ : Type v) [CommRing Λ] (K L : EtaleDerived A Λ) :
    (derivedTensor (etaleDatum.{u, v} B) (Coeff.{u, v} Λ)).obj
        (((etaleModules.{u, v} g).push (Coeff.{u, v} Λ)).obj K,
          ((etaleModules.{u, v} g).push (Coeff.{u, v} Λ)).obj L) ⟶
      ((etaleModules.{u, v} g).push (Coeff.{u, v} Λ)).obj
        ((derivedTensor (etaleDatum.{u, v} A) (Coeff.{u, v} Λ)).obj (K, L)) :=
  ((etaleModules.{u, v} g).adj (Coeff.{u, v} Λ)).homEquiv _ _
    ((pullTensor (etaleModules.{u, v} g) (Coeff.{u, v} Λ)).hom.app
        (((etaleModules.{u, v} g).push (Coeff.{u, v} Λ)).obj K,
          ((etaleModules.{u, v} g).push (Coeff.{u, v} Λ)).obj L) ≫
      (derivedTensor (etaleDatum.{u, v} A) (Coeff.{u, v} Λ)).map
        (Prod.mkHom (((etaleModules.{u, v} g).adj (Coeff.{u, v} Λ)).counit.app K)
          (((etaleModules.{u, v} g).adj (Coeff.{u, v} Λ)).counit.app L)))

/-- Strict-local inverse images detect isomorphisms of unbounded derived objects.
Source: Zheng proof of A.3; ILO XI 1.8, 1.10
(blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: each specialization-triple point is a geometric point of one Y_(y), followed
by σ_x, since its specialization factors through that strict localization. The
conservative triple-point theorem therefore detects sheaf isomorphisms. Exact
inverse images commute with every cohomology sheaf, so the same argument detects
vanishing of the cone of an arbitrary unbounded derived map. -/
theorem strictLocalSigma_jointly_conservative {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Λ : Type v) [CommRing Λ] {K L : VanishingDerived f Λ} (a : K ⟶ L) :
    IsIso a ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      IsIso (((strictLocalSigmaModules.{u, v} f x).pull (Coeff.{u, v} Λ)).map a) := by
  sorry

/-- Restricting the specified lax tensor map gives the direct-image tensor-of-counits map.
Source: Zheng proof of A.3, (A.3.1); Illusie §1.12
(blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: σ_x preserves derived tensor by the canonical pullTensor comparison. Unfold
both lax maps as adjunction transposes, the description comparison as the ordinary
comparison and inverse local-projection unit, and the p₂ψ identification. Naturality
moves the two counits to the final tensor factors; each intervening unit followed by
its counit cancels by the triangle identity. The resulting adjunct is the tensor of
the two direct-image counits, followed by the inverse tensor comparison for j. -/
theorem strictLocalDescription_laxTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (Λ : Type v) [CommRing Λ]
    (m : ℕ) (hm : 1 ≤ m) (hΛ : ∀ a : Λ, (m : Λ) * a = 0)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (K L : EtaleDerived X Λ) :
    ((strictLocalSigmaModules.{u, v} f x).pull (Coeff.{u, v} Λ)).map (laxTensor f Λ K L) ≫
        (strictLocalDescriptionComparison.{u, v} f x Λ).app
          ((derivedTensor (etaleDatum.{u, v} X) (Coeff.{u, v} Λ)).obj (K, L)) =
      (pullTensor (strictLocalSigmaModules.{u, v} f x) (Coeff.{u, v} Λ)).hom.app
          ((nearbyCycles.{u, v} f Λ).obj K, (nearbyCycles.{u, v} f Λ).obj L) ≫
        (derivedTensor (etaleDatum.{u, v} (Scheme.strictHenselizationScheme (x ≫ f)))
          (Coeff.{u, v} Λ)).map
          (Prod.mkHom ((strictLocalDescriptionComparison.{u, v} f x Λ).app K)
            ((strictLocalDescriptionComparison.{u, v} f x Λ).app L)) ≫
        strictLocalDirectLax.{u, v} (Scheme.strictHenselizationMap f x) Λ
          (((etaleModules.{u, v} (Scheme.strictHenselizationStructuralMap x)).pull (Coeff.{u, v}
            Λ)).obj K)
          (((etaleModules.{u, v} (Scheme.strictHenselizationStructuralMap x)).pull (Coeff.{u, v}
            Λ)).obj L) ≫
        ((etaleModules.{u, v} (Scheme.strictHenselizationMap f x)).push (Coeff.{u, v} Λ)).map
          ((pullTensor (etaleModules.{u, v} (Scheme.strictHenselizationStructuralMap x))
            (Coeff.{u, v} Λ)).inv.app (K, L)) := by
  sorry

/-- Ψ-goodness is exactly localized base-change invariance of all strict-local images,
and this invariance survives every further essentially Cartesian local square.
Source: Zheng Remark A.2(1), (A.2.1)
(blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: localize an arbitrary global base change at a geometric source point. The
functorial local square is essentially Cartesian: ind-étale invariance identifies
strict localizations after the two base changes, and the diagonal of Y_(y)/Y is the
strict localization at its diagonal closed point. The affine ind-étale base-change
and closed-point-localization lemmas identify the source with the required strict
localization of the fibre product. The ordinary-comparison compatibility identifies
its restriction with the displayed counit mate. Joint conservativity proves that
local invariance implies Ψ-goodness. Conversely, every essentially Cartesian local
square comes from localizing a global base change Y' → Y_(y) → Y, so Ψ-goodness makes
its mate invertible. For another such square, compose the global base changes. Mates
compose, since the middle unit and counit cancel. Thus Ψ-goodness survives that base
change and the same local test proves the final stability assertion. -/
theorem strictLocalDescription_baseChangeCriterion_core {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (Λ : Type v) [CommRing Λ]
    (m : ℕ) (hm : 1 ≤ m) (hΛ : ∀ a : Λ, (m : Λ) * a = 0)
    (K : EtaleDerived X Λ) :
    (IsPsiGood f Λ K ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : Spec (.of Ω) ⟶ X),
      HasLocalizedBaseChange (Scheme.strictHenselizationMap f x) Λ
        (((etaleModules.{u, v} (Scheme.strictHenselizationStructuralMap x)).pull
          (Coeff.{u, v} Λ)).obj K)) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      HasLocalizedBaseChange (Scheme.strictHenselizationMap f x) Λ
        (((etaleModules.{u, v} (Scheme.strictHenselizationStructuralMap x)).pull (Coeff.{u, v}
          Λ)).obj K) →
      ∀ S : StrictLocalTestSquare (Scheme.strictHenselizationMap f x),
        HasLocalizedBaseChange S.g' Λ
          (((etaleModules.{u, v} S.h).pull (Coeff.{u, v} Λ)).obj
            (((etaleModules.{u, v} (Scheme.strictHenselizationStructuralMap x)).pull
              (Coeff.{u, v} Λ)).obj K))) := by
  sorry

/-- The point-composition iso is fixed on every skyscraper product projection by the
actual pullback equivalence of pointed étale lifts.
Source: Illusie §1.11; Stacks 03Q1
(blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: at V, reindex the product by pointSmallEtaleFiberEtaleIso. The pullback universal
property makes the reindexing natural in V, and products make it natural in M. Each
projection fixes the map uniquely, and the inverse reindexing gives its inverse. -/
theorem strictLocalPointComp_existsUnique {A B : Scheme.{u}} (a : A ⟶ B)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ A) :
    ∃! e : ((localPoint.{u, v} x).comp (etaleMorphism a)).direct ≅
        (localPoint.{u, v} (x ≫ a)).direct,
      ∀ (M : Type (max (u + 1) v)) (V : EtaleSite.{u, v} B)
        (l : (Scheme.pointSmallEtale (x ≫ a)).fiber.obj (AsSmall.down.obj V)),
        ((e.hom.app M).hom.app (op V)) ≫
            Pi.π (fun _ : (Scheme.pointSmallEtale (x ≫ a)).fiber.obj
              (AsSmall.down.obj V) ↦ M) l =
          Pi.π (fun _ : (Scheme.pointSmallEtale x).fiber.obj
            (a.Etale.obj (AsSmall.down.obj V)) ↦ M)
            ((Scheme.pointSmallEtaleFiberEtaleIso a x).inv.app (AsSmall.down.obj V) l) := by
  sorry

/-- The canonical point-composition iso, including the normalization on pointed lifts.
Source: Illusie §1.11 (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalPointComp {A B : Scheme.{u}} (a : A ⟶ B)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ A) :=
  (strictLocalPointComp_existsUnique.{u, v} a x).choose

/-- The first projection of σ_x is the constant geometric point x.
Source: Illusie (1.11.4)--(1.11.5)
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalSigmaFirst {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ((strictLocalSigma.{u, v} f x).comp (p₁ f)).direct ≅
      ((localEpsilon.{u, v} (Scheme.strictHenselizationScheme (x ≫ f))).comp (localPoint.{u, v}
        x)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (strictLocalLift.{u, v} f x).morphism.direct
      (squareLift f (Scheme.strictHenselizationMap f x)
        (Scheme.strictHenselizationStructuralMap x)
        (Scheme.strictHenselizationStructuralMap (x ≫ f))
        (Scheme.strictHenselizationMap_over f x).symm).first ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (strictLocalLift.{u, v} f x).first _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (strictLocalPointComp.{u, v} (Scheme.strictHenselizationStructuralMap x) (strictLocalPoint
        x) ≪≫
        eqToIso (congrArg (fun z ↦ (localPoint.{u, v} z).direct)
          (Scheme.strictHenselizationClosedLift_over x)))

/-- The second projection of σ_x is the structural strict-localization map.
Source: Illusie (1.11.4)--(1.11.5)
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalSigmaSecond {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ((strictLocalSigma.{u, v} f x).comp (p₂ f)).direct ≅
      (etaleMorphism (Scheme.strictHenselizationStructuralMap (x ≫ f))).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (strictLocalLift.{u, v} f x).morphism.direct
      (squareLift f (Scheme.strictHenselizationMap f x)
        (Scheme.strictHenselizationStructuralMap x)
        (Scheme.strictHenselizationStructuralMap (x ≫ f))
        (Scheme.strictHenselizationMap_over f x).symm).second ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (strictLocalLift.{u, v} f x).second _ ≪≫ Functor.leftUnitor _

/-- Equality of the image geometric points in a commutative scheme square.
Source: Illusie §1.11 (blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: reassociate x' followed by h then f, apply the square equation, and reassociate. -/
theorem strictLocalSquarePoint_eq {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : X' ⟶ X) (k : Y' ⟶ Y) (comm : h ≫ f = f' ≫ k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x' : Spec (.of Ω) ⟶ X') :
    (x' ≫ f') ≫ k = (x' ≫ h) ≫ f := by
  sorry

/-- The functorial local map on the base, with its geometric-point equality transport.
Source: Zheng Remark A.2(1); Illusie §1.11
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalSquareBase {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : X' ⟶ X) (k : Y' ⟶ Y) (comm : h ≫ f = f' ≫ k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x' : Spec (.of Ω) ⟶ X') :
    Scheme.strictHenselizationScheme (x' ≫ f') ⟶
      Scheme.strictHenselizationScheme ((x' ≫ h) ≫ f) :=
  Scheme.strictHenselizationMap k (x' ≫ f') ≫
    eqToHom (congrArg Scheme.strictHenselizationScheme
      (strictLocalSquarePoint_eq.{u} f f' h k comm x'))

/-- The structural equation for the canonical base map of the local square.
Source: Stacks 04GU (blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: substitute the image-point equality in strictHenselizationMap_over for k. -/
theorem strictLocalSquareBase_over {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : X' ⟶ X) (k : Y' ⟶ Y) (comm : h ≫ f = f' ≫ k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x' : Spec (.of Ω) ⟶ X') :
    strictLocalSquareBase.{u} f f' h k comm x' ≫
        Scheme.strictHenselizationStructuralMap ((x' ≫ h) ≫ f) =
      Scheme.strictHenselizationStructuralMap (x' ≫ f') ≫ k := by
  sorry

/-- The functorial local square commutes with its specified image-point transports.
Source: Stacks 04GU; Zheng Remark A.2(1)
(blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: both composites are pointed maps from X'_(x') to Y_(f(h(x'))), over the same
scheme map. Uniqueness in strictHenselizationMap_existsUnique identifies them. -/
theorem strictLocalSquare_comm {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : X' ⟶ X) (k : Y' ⟶ Y) (comm : h ≫ f = f' ≫ k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x' : Spec (.of Ω) ⟶ X') :
    Scheme.strictHenselizationMap h x' ≫ Scheme.strictHenselizationMap f (x' ≫ h) =
      Scheme.strictHenselizationMap f' x' ≫ strictLocalSquareBase.{u} f f' h k comm x' := by
  sorry

/-- The first projection of vσ_x', normalized to the constant point h(x').
Source: Illusie §1.11 (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalSquareFirstLeft {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : X' ⟶ X) (k : Y' ⟶ Y) (comm : h ≫ f = f' ≫ k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x' : Spec (.of Ω) ⟶ X') :
    (((strictLocalSigma.{u, v} f' x').comp (squareMorphism f f' h k comm)).comp (p₁ f)).direct ≅
      ((localEpsilon.{u, v} (Scheme.strictHenselizationScheme (x' ≫ f'))).comp
        (localPoint.{u, v} (x' ≫ h))).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (squareLift f f' h k comm).first ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (strictLocalSigmaFirst.{u, v} f' x') _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (strictLocalPointComp.{u, v} h x')

/-- The first projection of σ_x k_(x'), normalized to the same constant point.
Source: Illusie §1.11 (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalSquareFirstRight {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : X' ⟶ X) (k : Y' ⟶ Y) (comm : h ≫ f = f' ≫ k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x' : Spec (.of Ω) ⟶ X') :
    (((etaleMorphism.{u, v} (strictLocalSquareBase.{u} f f' h k comm x')).comp
      (strictLocalSigma.{u, v} f (x' ≫ h))).comp (p₁ f)).direct ≅
      ((localEpsilon.{u, v} (Scheme.strictHenselizationScheme (x' ≫ f'))).comp
        (localPoint.{u, v} (x' ≫ h))).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (strictLocalSigmaFirst.{u, v} f (x' ≫ h)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (localDirectSections.{u, v} (strictLocalSquareBase.{u} f f' h k comm
      x')) _

/-- The second projection of vσ_x', with the canonical composition comparison.
Source: Illusie §1.11 (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalSquareSecondLeft {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : X' ⟶ X) (k : Y' ⟶ Y) (comm : h ≫ f = f' ≫ k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x' : Spec (.of Ω) ⟶ X') :
    (((strictLocalSigma.{u, v} f' x').comp (squareMorphism f f' h k comm)).comp (p₂ f)).direct ≅
      (etaleMorphism (Scheme.strictHenselizationStructuralMap (x' ≫ f') ≫ k)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (squareLift f f' h k comm).second ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (strictLocalSigmaSecond.{u, v} f' x') _ ≪≫ etaleComposition _ _

/-- The second projection of σ_x k_(x'), with the same structural-map normalization.
Source: Illusie §1.11 (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalSquareSecondRight {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : X' ⟶ X) (k : Y' ⟶ Y) (comm : h ≫ f = f' ≫ k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x' : Spec (.of Ω) ⟶ X') :
    (((etaleMorphism.{u, v} (strictLocalSquareBase.{u} f f' h k comm x')).comp
      (strictLocalSigma.{u, v} f (x' ≫ h))).comp (p₂ f)).direct ≅
      (etaleMorphism (Scheme.strictHenselizationStructuralMap (x' ≫ f') ≫ k)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (strictLocalSigmaSecond.{u, v} f (x' ≫ h)) ≪≫
    etaleComposition _ _ ≪≫ eqToIso
      (congrArg (fun a ↦ (etaleMorphism.{u, v} a).direct)
        (strictLocalSquareBase_over.{u} f f' h k comm x'))

/-- The two strict-local section composites have a unique projection-compatible iso.
Source: Illusie §1.11; ILO XI 1.4
(blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: normalize both first projections to the constant point h(x') and both second
projections to the same structural map. Naturality of the closed-point counit makes
the pasted orientations equal. The uniqueness clause of the oriented-product universal
property supplies exactly one isomorphism satisfying these two projection equations. -/
theorem strictLocalSigmaSquare_existsUnique {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (h : X' ⟶ X) (k : Y' ⟶ Y)
    (comm : h ≫ f = f' ≫ k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x' : Spec (.of Ω) ⟶ X') :
    ∃! e : ((strictLocalSigma.{u, v} f' x').comp (squareMorphism f f' h k comm)).direct ≅
        ((etaleMorphism (strictLocalSquareBase.{u} f f' h k comm x')).comp
          (strictLocalSigma.{u, v} f (x' ≫ h))).direct,
      Functor.isoWhiskerRight e (p₁ f).direct ≪≫
          strictLocalSquareFirstRight.{u, v} f f' h k comm x' =
        strictLocalSquareFirstLeft.{u, v} f f' h k comm x' ∧
      Functor.isoWhiskerRight e (p₂ f).direct ≪≫
          strictLocalSquareSecondRight.{u, v} f f' h k comm x' =
        strictLocalSquareSecondLeft.{u, v} f f' h k comm x' := by
  sorry

/-- The canonical square of σ sections, with both projections and orientation fixed.
Source: Illusie §1.11 (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalSigmaSquare {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : X' ⟶ X) (k : Y' ⟶ Y) (comm : h ≫ f = f' ≫ k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x' : Spec (.of Ω) ⟶ X') :=
  (strictLocalSigmaSquare_existsUnique.{u, v} f f' h k comm x').choose

/-- Exact localization of the canonical σ square to constant-coefficient modules.
Source: Illusie §1.11 (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalSigmaPullSquare {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : X' ⟶ X) (k : Y' ⟶ Y) (comm : h ≫ f = f' ≫ k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x' : Spec (.of Ω) ⟶ X')
    (Λ : Type v) [CommRing Λ] :
    (squareModules.{u, v} f f' h k comm).pull (Coeff.{u, v} Λ) ⋙
        (strictLocalSigmaModules.{u, v} f' x').pull (Coeff Λ) ≅
      (strictLocalSigmaModules.{u, v} f (x' ≫ h)).pull (Coeff Λ) ⋙
        (etaleModules (strictLocalSquareBase.{u} f f' h k comm x')).pull (Coeff Λ) :=
  derivedSquare (f := strictLocalSigmaModules.{u, v} f (x' ≫ h))
    (g := squareModules f f' h k comm)
    (h := etaleModules (strictLocalSquareBase.{u} f f' h k comm x'))
    (k := strictLocalSigmaModules.{u, v} f' x')
    (GeometricMorphism.inverseIso (strictLocalSigmaSquare.{u, v} f f' h k comm x')).symm (Coeff Λ)

/-- The direct-image comparison on localizations, transported only along its canonical
pointed source square, to the actual restriction of h*L.
Source: Zheng Remark A.2(1); (A.3.1)
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalRestrictedComparison {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (h : X' ⟶ X) (k : Y' ⟶ Y) (comm : h ≫ f = f' ≫ k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x' : Spec (.of Ω) ⟶ X')
    (Λ : Type v) [CommRing Λ] (L : EtaleDerived X Λ) :
    ((strictLocalSigmaModules.{u, v} f' x').pull (Coeff.{u, v} Λ)).obj
        (((squareModules f f' h k comm).pull (Coeff Λ)).obj ((nearbyCycles f Λ).obj L)) ⟶
      ((etaleModules (Scheme.strictHenselizationMap f' x')).push (Coeff Λ)).obj
        (((etaleModules (Scheme.strictHenselizationStructuralMap x')).pull (Coeff Λ)).obj
          (((etaleModules h).pull (Coeff Λ)).obj L)) :=
  (strictLocalSigmaPullSquare.{u, v} f f' h k comm x' Λ).hom.app ((nearbyCycles f Λ).obj L) ≫
    ((etaleModules (strictLocalSquareBase.{u} f f' h k comm x')).pull (Coeff Λ)).map
      ((strictLocalDescriptionComparison.{u, v} f (x' ≫ h) Λ).app L) ≫
    strictLocalDirectBaseChange.{u, v} (Scheme.strictHenselizationMap f (x' ≫ h))
      (Scheme.strictHenselizationMap f' x') (Scheme.strictHenselizationMap h x')
      (strictLocalSquareBase.{u} f f' h k comm x') (strictLocalSquare_comm.{u} f f' h k comm x') Λ
      (((etaleModules (Scheme.strictHenselizationStructuralMap (x' ≫ h))).pull
        (Coeff Λ)).obj L) ≫
    ((etaleModules (Scheme.strictHenselizationMap f' x')).push (Coeff Λ)).map
      ((strictLocalDirectSquare.{u, v} h (Scheme.strictHenselizationMap h x')
        (Scheme.strictHenselizationStructuralMap x')
        (Scheme.strictHenselizationStructuralMap (x' ≫ h))
        (Scheme.strictHenselizationMap_over h x').symm Λ).hom.app L)

/-- Ordinary nearby comparisons become the actual ordinary direct-image counit mates.
No invertibility is assumed in this compatibility assertion.
Source: Zheng Remark A.2(1); Illusie §1.12
(blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: the normalized σ square has the same closed-point counit orientation on both
sides. Expand the ordinary nearby mate, the local-projection unit, and the description
comparison. After moving the square isomorphisms past the adjunction units, the middle
unit and counit cancel. The adjunct is g'^*k^*Rg_*L → h^*L given by h^*ε_g, exactly
the defining adjunct of strictLocalDirectBaseChange.{u, v}. This proves the equation. -/
theorem strictLocalDescription_ordinaryComparison {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (h : X' ⟶ X) (k : Y' ⟶ Y)
    (comm : h ≫ f = f' ≫ k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x' : Spec (.of Ω) ⟶ X')
    (Λ : Type v) [CommRing Λ] (L : EtaleDerived X Λ) :
    ((strictLocalSigmaModules.{u, v} f' x').pull (Coeff.{u, v} Λ)).map
        (baseChange f f' h k comm Λ L) ≫
      (strictLocalDescriptionComparison.{u, v} f' x' Λ).app
        (((etaleModules h).pull (Coeff Λ)).obj L) =
      strictLocalRestrictedComparison.{u, v} f f' h k comm x' Λ L := by
  sorry

/-- The direct-image external-product comparison on the strict localizations of both
factors and their product. The product scheme itself is never assumed strictly local.
Source: Zheng (A.3.1) (blueprint: lem-trf-oriented-nearby-strict-local-description). -/
def strictLocalExternalComparison {X₁ X₂ Y : Scheme.{u}} (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ pullback f₁ f₂)
    (Λ : Type v) [CommRing Λ] (L₁ : EtaleDerived X₁ Λ) (L₂ : EtaleDerived X₂ Λ) :
    ((strictLocalSigmaModules.{u, v} (productMap f₁ f₂) x).pull (Coeff.{u, v} Λ)).obj
        (externalVanishing f₁ f₂ Λ ((nearbyCycles f₁ Λ).obj L₁)
          ((nearbyCycles f₂ Λ).obj L₂)) ⟶
      ((etaleModules (Scheme.strictHenselizationMap (productMap f₁ f₂) x)).push
        (Coeff Λ)).obj
        (((etaleModules (Scheme.strictHenselizationStructuralMap x)).pull (Coeff Λ)).obj
          (externalEtale f₁ f₂ Λ L₁ L₂)) :=
  let f := productMap f₁ f₂
  let j := Scheme.strictHenselizationStructuralMap x
  let g := Scheme.strictHenselizationMap f x
  let q₁ := pullback.fst f₁ f₂
  let q₂ := pullback.snd f₁ f₂
  let A := Coeff.{u, v} Λ
  let c₁ := product_first_comm f₁ f₂
  let c₂ := product_second_comm f₁ f₂
  let s := strictLocalSigmaModules.{u, v} f x
  let n₁ := ((productFirst f₁ f₂).pull A).obj ((nearbyCycles f₁ Λ).obj L₁)
  let n₂ := ((productSecond f₁ f₂).pull A).obj ((nearbyCycles f₂ Λ).obj L₂)
  let k₁ := ((etaleModules q₁).pull A).obj L₁
  let k₂ := ((etaleModules q₂).pull A).obj L₂
  (pullTensor s A).hom.app (n₁, n₂) ≫
    (derivedTensor (etaleDatum (Scheme.strictHenselizationScheme (x ≫ f))) A).map
      (Prod.mkHom (strictLocalRestrictedComparison.{u, v} f₁ f q₁ (𝟙 Y) c₁ x Λ L₁)
        (strictLocalRestrictedComparison.{u, v} f₂ f q₂ (𝟙 Y) c₂ x Λ L₂)) ≫
    strictLocalDirectLax.{u, v} g Λ (((etaleModules j).pull A).obj k₁)
      (((etaleModules j).pull A).obj k₂) ≫
    ((etaleModules g).push A).map ((pullTensor (etaleModules j) A).inv.app (k₁, k₂))

/-- The specified oriented external-product comparison restricts to the direct-image
external-product comparison on all three strict localizations.
Source: Zheng proof of Theorem A.3, (A.3.1)
(blueprint: lem-trf-oriented-nearby-strict-local-description).
Proof: by definition kunneth is the tensor of the two ordinary comparisons followed
by the lax tensor map. Pull this composite back by σ_x and apply the canonical tensor
comparison. The ordinary-comparison identity identifies its first two factors with
the direct-image comparisons for the functorial strict-local projection squares.
The lax-tensor identity identifies the last factor with the tensor-of-counits mate.
Their composite is precisely strictLocalExternalComparison.{u, v}, with the inverse tensor
comparison for the structural map j accounting for its final target. -/
theorem strictLocalDescription_externalProduct {X₁ X₂ Y : Scheme.{u}}
    (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂]
    (Λ : Type v) [CommRing Λ] (m : ℕ) (hm : 1 ≤ m)
    (hΛ : ∀ a : Λ, (m : Λ) * a = 0)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ pullback f₁ f₂)
    (L₁ : EtaleDerived X₁ Λ) (L₂ : EtaleDerived X₂ Λ) :
    ((strictLocalSigmaModules.{u, v} (productMap f₁ f₂) x).pull (Coeff.{u, v} Λ)).map
        (kunneth f₁ f₂ Λ L₁ L₂) ≫
      (strictLocalDescriptionComparison.{u, v} (productMap f₁ f₂) x Λ).app
        (externalEtale f₁ f₂ Λ L₁ L₂) =
      strictLocalExternalComparison.{u, v} f₁ f₂ x Λ L₁ L₂ := by
  sorry

/-- Complete strict-local description package: exact and tensor-preserving canonical sections,
joint conservativity, comparison compatibilities, and localized base-change criterion.
Source: Zheng Appendix A.2--A.3 and Illusie (1.11)--(1.12)
(blueprint: lem-trf-oriented-nearby-strict-local-description). -/
theorem strictLocalDescription_baseChangeCriterion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (Λ : Type v) [CommRing Λ]
    (m : ℕ) (hm : 1 ≤ m) (hΛ : ∀ a : Λ, (m : Λ) * a = 0)
    (K : EtaleDerived X Λ) :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      PreservesFiniteLimits ((strictLocalSigmaModules.{u, v} f x).pull (Coeff.{u, v} Λ)) ∧
      (∀ A B : VanishingDerived f Λ, IsIso ((pullTensor (strictLocalSigmaModules.{u, v} f x)
        (Coeff.{u, v} Λ)).hom.app (A, B))) ∧
      IsIso (strictLocalDescriptionComparison.{u, v} f x Λ)) ∧
    (∀ {A B : VanishingDerived f Λ} (a : A ⟶ B),
      IsIso a ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        IsIso (((strictLocalSigmaModules.{u, v} f x).pull (Coeff.{u, v} Λ)).map a)) ∧
    (∀ {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') (h : X' ⟶ X) (k : Y' ⟶ Y)
      (comm : h ≫ f = f' ≫ k) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
      (x' : Spec (.of Ω) ⟶ X') (L : EtaleDerived X Λ),
      ((strictLocalSigmaModules.{u, v} f' x').pull (Coeff.{u, v} Λ)).map
          (baseChange f f' h k comm Λ L) ≫
        (strictLocalDescriptionComparison.{u, v} f' x' Λ).app
          (((etaleModules h).pull (Coeff Λ)).obj L) =
      strictLocalRestrictedComparison.{u, v} f f' h k comm x' Λ L) ∧
    (∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
      (A B : EtaleDerived X Λ),
      IsIso (((strictLocalSigmaModules.{u, v} f x).pull (Coeff.{u, v} Λ)).map
        (laxTensor f Λ A B))) ∧
    (∀ {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
      [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂]
      (L₁ : EtaleDerived X₁ Λ) (L₂ : EtaleDerived X₂ Λ)
      {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
      (x : Spec (.of Ω) ⟶ pullback f₁ f₂),
      IsIso (((strictLocalSigmaModules.{u, v} (productMap f₁ f₂) x).pull
        (Coeff.{u, v} Λ)).map (kunneth f₁ f₂ Λ L₁ L₂))) ∧
    (IsPsiGood f Λ K ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : Spec (.of Ω) ⟶ X),
      HasLocalizedBaseChange (Scheme.strictHenselizationMap f x) Λ
        (((etaleModules.{u, v} (Scheme.strictHenselizationStructuralMap x)).pull
          (Coeff.{u, v} Λ)).obj K)) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
      HasLocalizedBaseChange (Scheme.strictHenselizationMap f x) Λ
        (((etaleModules.{u, v} (Scheme.strictHenselizationStructuralMap x)).pull
          (Coeff.{u, v} Λ)).obj K) →
      ∀ S : StrictLocalTestSquare (Scheme.strictHenselizationMap f x),
        HasLocalizedBaseChange S.g' Λ
          (((etaleModules.{u, v} S.h).pull (Coeff.{u, v} Λ)).obj
            (((etaleModules.{u, v} (Scheme.strictHenselizationStructuralMap x)).pull
              (Coeff.{u, v} Λ)).obj K))) := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles
