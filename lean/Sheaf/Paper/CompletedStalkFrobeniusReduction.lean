/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntegralOperationsPreserveConstructible
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
public import Sheaf.Paper.LocalFrobeniusTransportNormalization
public import Sheaf.Paper.PointReductionUnitNormalization
public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.PointReductionUnits
public import Sheaf.Paper.IntegralFinitePullbackComposition
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.Paper.FrobeniusCoefficientReductionCoherence
import Sheaf.Paper.PointSectionsFiniteReduction
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Paper.TraceFormulaLocalFrobeniusOperator
import Sheaf.Paper.FixedStalkIdentificationReduction

/-!
# Reduction of completed stalk Frobenius transport

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (4)
(blueprint: lem-trf-completed-stalk-frobenius-reduction).

## Main definitions

* `reduction`: the canonical completed-pullback and point-sections reduction isomorphism.
* `finiteTransport` and `integralTransport`: the published normalized transports in
  composite-pullback coordinates, transported through the identity localization functor.
* `ReductionStatement`: the reduction square, quotient compatibility and naturality.

## Main statements

* `completedStalkFrobeniusReduction`: the complete reduction assertion.

The finite exponent is n+1. Target stalks use composite-pullback coordinates;
the canonical compositor identifies these with the stalk of the Galois pullback.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.CompletedStalkFrobenius

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Canonical change from the small Grothendieck localization to the standard one.
It is induced by the identity exact functor on coefficient modules, preserving scalars.
Source: Mathlib localization universal property; blueprint integral-model proof (4)
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def moduleSizeLift (R : Type (u + 1)) [CommRing R] :=
  @Functor.mapDerivedCategory (ModuleCat.{u + 1} R) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian _) (ModuleCat.{u + 1} R) _ _
    (HasDerivedCategory.standard _) (𝟭 (ModuleCat.{u + 1} R)) inferInstance
    inferInstance inferInstance

/-- Large-Hom integral sections, retaining exactly the coefficient-module action.
Source: blueprint integral-model proof (4), size transport of exact sections
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def integralSectionsLarge :=
  @Functor.mapDerivedCategory (integralTowerModules l E (Spec (.of D.k))) _ _
    (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _
    (HasDerivedCategory.standard _) (pointIntegralSections l E D.k)
    (pointIntegralSectionsAdditive l E D.k)
    (pointFibreIntegralLimits D l E) (pointFibreIntegralColimits D l E)

/-- Large-Hom finite sections, using the same scalar action and same final-object sections.
Source: blueprint integral-model proof (4), size transport of exact sections
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def finiteSectionsLarge (n : ℕ) :=
  @Functor.mapDerivedCategory (integralOperationsFiniteModules l E (Spec (.of D.k)) n) _ _
    (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) _ _
    (HasDerivedCategory.standard _)
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFiniteSectionsAdditive D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteLimits D (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteColimits D (Padic.coefficientExtensionRing l E (n + 1)))

/-- Exact sections commute with canonical localization-size transport.
Source: localization universal property; blueprint integral-model proof (4)
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def integralSectionsSize :
    pointFibreIntegralAmbient D l E ⋙
        moduleSizeLift (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) ≅
      integralSectionsLarge D l E :=
  (@Functor.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _
    (HasDerivedCategory.standard _) (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (HasDerivedCategory.standard _) (pointIntegralSections l E D.k)
    (𝟭 (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))
    (pointIntegralSectionsAdditive l E D.k) inferInstance
    (pointFibreIntegralLimits D l E) (pointFibreIntegralColimits D l E)
    inferInstance inferInstance).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.rightUnitor (pointIntegralSections l E D.k))

/-- The corresponding normalized comparison for finite sections.
Source: localization universal property; blueprint integral-model proof (4)
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def finiteSectionsSize (n : ℕ) :
    LocalFrobeniusTransport.finiteSectionsDerived D l E n ⋙
        moduleSizeLift (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) ≅
      finiteSectionsLarge D l E n :=
  letI := pointFiniteSectionsAdditive D.k (Padic.coefficientExtensionRing l E (n + 1))
  (@Functor.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _
    (HasDerivedCategory.standard _) (HasDerivedCategory.ofIsGrothendieckAbelian _)
    (HasDerivedCategory.standard _)
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
    (𝟭 (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))
    inferInstance inferInstance
    (pointFibreFiniteLimits D (Padic.coefficientExtensionRing l E (n + 1)))
    (pointFibreFiniteColimits D (Padic.coefficientExtensionRing l E (n + 1)))
    inferInstance inferInstance).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Functor.rightUnitor
        (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))))


/-- Exact integral sections with the same standard localization used by coefficient units.
Source: localization universal property; blueprint integral-model proof (4)
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def integralSectionsLargeFactors :=
  @Functor.mapDerivedCategoryFactors (integralTowerModules l E (Spec (.of D.k))) _ _
    (HasDerivedCategory.standard _)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _
    (HasDerivedCategory.standard _) (pointIntegralSections l E D.k)
    (pointIntegralSectionsAdditive l E D.k)
    (pointFibreIntegralLimits D l E) (pointFibreIntegralColimits D l E)

/-- The recorded completed stalk, canonically transported only in localization size.
Source: blueprint integral-model proof (4), definition of S
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def integralFibreLarge {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X) :=
  (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E v ⋙
    integralSectionsLarge D l E

/-- Localization of integral section complexes in the same standard target model.
Source: Mathlib DerivedCategory.Q; blueprint integral-model proof (4)
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
abbrev moduleQLarge :=
  @DerivedCategory.Q
    (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) _ _
    (HasDerivedCategory.standard _)

/-- The canonical point reduction comparison, selected with its unique unit normalization.
Source: blueprint integral-model proof (4), Stacks 07A6
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def sectionsReduction (n : ℕ) :=
  ((pointReductionUnitNormalization D l E hl).1 n).exists.choose

/-- Finite stalk sections in the same coefficient and localization universes.
Source: blueprint integral-model proof (4), definition of S_n
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def finiteFibre {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X) (n : ℕ) :=
  proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) v ⋙
    finiteSectionsLarge D l E n

variable [hpoint : ∀ x : Spec (.of D.k),
    Invertible (l : (Spec (.of D.k)).residueField x)]

/-- Alpha is point-sections reduction followed by the actual pullback-reduction map.
It uses the projection-adjoint comparison, not an arbitrary isomorphism of stalks.
Source: blueprint integral-model proof (4), first reduction identification
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def reduction {X : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    (v : Spec (.of D.k) ⟶ X) (K : sfIntegralConstructibleCategory l E X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) (n : ℕ) :=
  (sectionsReduction D l hl E n).app ((constructibleIntegralPullback l E v).obj K) ≪≫
    (finiteSectionsLarge D l E n).mapIso
      (integralPullbackReductionIso l E v K P e n)

/-- The restricted finite model of the stalk reduction, with its canonical localization maps.
Source: blueprint integral-model proof (4), actual limit projections
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def finiteModel {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X)
    (K : sfIntegralConstructibleCategory l E X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) (n : ℕ) :=
  (finiteSectionsLarge D l E n).mapIso
    ((proEtaleConstantRingDerivedPullback
      (Padic.coefficientExtensionRing l E (n + 1)) v).mapIso
      ((scalarReductionDerivedExtension l E X n).mapIso e.symm ≪≫
        coefficientFiniteReductionModel l E X P.obj P.property.1 n)) ≪≫
  (finiteSectionsLarge D l E n).mapIso
    ((proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1))
      v).mapDerivedCategoryFactors.app
      ((unrestrictedIntegralFiniteComplex l E X n).obj P.obj)) ≪≫
  (finiteSectionsLarge D l E n).mapIso
    (DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E v n)
        (.up ℤ)).app
          ((unrestrictedIntegralFiniteComplex l E X n).obj P.obj))).symm

/-- The finite normalized transport in composite-pullback coordinates. The last arrow
is exactly the finite pullback compositor, so its target is the reduction of the
same direct completed pullback used by integralNormalized.
Source: blueprint integral-model proof (4), normalized tau
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def finiteTransport
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (n m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm)
    (K : proEtaleDerivedCategory (D.geometricFiber X₀).left
      (Padic.coefficientExtensionRing l E (n + 1))) :=
  (finiteSectionsSize D l E n).inv.app
      ((proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
        (localExtensionPoint D X₀ m hm y)).obj K) ≫
    (moduleSizeLift (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))).map
      (LocalFrobeniusTransport.finiteNormalized D l hl E X₀ n m hm y K ≫
        (LocalFrobeniusTransport.finiteSectionsDerived D l E n).map
          ((proEtaleConstantRingPullbackComposition (localExtensionPoint D X₀ m hm y)
            ((End.of (D.geometricGaloisFrobenius X₀)) ^ m)
            (Padic.coefficientExtensionRing l E (n + 1))).hom.app K)) ≫
    (finiteSectionsSize D l E n).hom.app
      ((proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
        (localExtensionPoint D X₀ m hm y ≫
          (End.of (D.geometricGaloisFrobenius X₀)) ^ m)).obj K)

/-- The specified whole-tower realization in the standard localization of modules.
The only added arrows are the canonical localization-size comparisons.
Source: blueprint integral-model proof (4), integral tau
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def integralTransport
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
    (P : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) :=
  (integralSectionsSize D l E).inv.app
      ((integralDerivedPullback l E (localExtensionPoint D X₀ m hm y)).obj K.obj) ≫
    (moduleSizeLift (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))).map
      (LocalFrobeniusTransport.integralNormalized D l hl E X₀ m hm y K P e) ≫
    (integralSectionsSize D l E).hom.app
      ((integralDerivedPullback l E
        (localExtensionPoint D X₀ m hm y ≫
          (End.of (D.geometricGaloisFrobenius X₀)) ^ m)).obj K.obj)

/-- The same finite computation after restriction to O_E, followed by exact sections.
Every factor is a recorded identity-on-sections or localization comparison.
Source: blueprint integral-model proof (4), proof Step 4
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def restrictedModel {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X)
    (K : sfIntegralConstructibleCategory l E X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) (n : ℕ) :=
  (pointUnitIntegralDerivedRestriction l E n).mapIso (finiteModel D l E v K P e n) ≪≫
    ((pointUnitIntegralDerivedSectionsRestrictionIso D l E n).app
      (DerivedCategory.Q.obj (integralPullbackFiniteComplex l E v P.obj n))).symm ≪≫
    (integralSectionsLarge D l E).mapIso
      ((scalarReductionRestriction l E (Spec (.of D.k)) n).mapDerivedCategoryFactors.app
        (integralPullbackFiniteComplex l E v P.obj n)) ≪≫
    (integralSectionsLargeFactors D l E).app
      ((((scalarReductionRestriction l E (Spec (.of D.k)) n).mapHomologicalComplex
        (.up ℤ)).obj (integralPullbackFiniteComplex l E v P.obj n)))

/-- The actual quotient transition, in the restricted finite-stalk coordinates.
It is the strict quotient tower arrow, transported through its canonical finite models.
Equal indices give the identity. No reduction is assumed flat.
Source: blueprint integral-model proof (4), compatibility with A_b to A_a
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def transition {X : Scheme.{u}} (v : Spec (.of D.k) ⟶ X)
    (K : sfIntegralConstructibleCategory l E X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) (b a : ℕ) (h : a ≤ b) :=
  (restrictedModel D l E v K P e b).hom ≫
    (moduleQLarge l E).map
      (((LocalFrobeniusTransport.strictTower D l E v).obj P.obj).map (homOfLE h).op) ≫
    (restrictedModel D l E v K P e a).inv

/-- The scalar-extension adjunct of the canonical completed stalk reduction.
Using adjuncts states quotient coherence without suppressing tensor associators:
the normalized successive-quotient adjunction identifies this with the usual
square for two successive derived scalar extensions.
Source: blueprint integral-model proof (4), proof Steps 4 and 6
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def reductionAdjoint {X : Scheme.{u}} [∀ x : X, Invertible (l : X.residueField x)]
    (v : Spec (.of D.k) ⟶ X) (K : sfIntegralConstructibleCategory l E X)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) (n : ℕ) :=
  (pointUnitIntegralModuleUnit l E n).app ((integralFibreLarge D l E v).obj K) ≫
    (pointUnitIntegralDerivedRestriction l E n).map (reduction D l hl E v K P e n).hom

/-- The reduction square, quotient coherence and naturality, using only the canonical
prime-to-p invertibility instances derived from the given coefficient convention.
Source: blueprint integral-model proof (4)
(blueprint: lem-trf-completed-stalk-frobenius-reduction). -/
def ReductionStatement
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) : Prop :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := D.schemeFrobeniusCoefficientInvertible X₀ l hl
  (∀ (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
      (_hK : ∀ n : ℕ, finiteTorConstructible l E (n + 1) (Nat.succ_pos n)
        (D.geometricFiber X₀).left
        ((scalarReductionDerivedExtension l E (D.geometricFiber X₀).left n).obj K.obj))
      (P : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory)
      (e : DerivedCategory.Q.obj P.obj ≅ K.obj) (n : ℕ),
      (pointReductionModuleTensor l E n).map
          (integralTransport D l hl E X₀ m hm y K P e) ≫
        (reduction D l hl E
          (localExtensionPoint D X₀ m hm y ≫
            (End.of (D.geometricGaloisFrobenius X₀)) ^ m) K P e n).hom =
      (reduction D l hl E (localExtensionPoint D X₀ m hm y) K P e n).hom ≫
        finiteTransport D l hl E X₀ n m hm y
          ((scalarReductionDerivedExtension l E (D.geometricFiber X₀).left n).obj K.obj)) ∧
    (∀ (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
      (_hK : ∀ n : ℕ, finiteTorConstructible l E (n + 1) (Nat.succ_pos n)
        (D.geometricFiber X₀).left
        ((scalarReductionDerivedExtension l E (D.geometricFiber X₀).left n).obj K.obj))
      (P : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory)
      (e : DerivedCategory.Q.obj P.obj ≅ K.obj)
      (v : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
      (_hv : v = localExtensionPoint D X₀ m hm y ∨
        v = localExtensionPoint D X₀ m hm y ≫
          (End.of (D.geometricGaloisFrobenius X₀)) ^ m)
      (b a : ℕ) (h : a ≤ b),
      reductionAdjoint D l hl E v K P e b ≫ transition D l E v K P e b a h =
        reductionAdjoint D l hl E v K P e a) ∧
    (∀ (K L : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
      (_hK : ∀ n : ℕ, finiteTorConstructible l E (n + 1) (Nat.succ_pos n)
        (D.geometricFiber X₀).left
        ((scalarReductionDerivedExtension l E (D.geometricFiber X₀).left n).obj K.obj))
      (_hL : ∀ n : ℕ, finiteTorConstructible l E (n + 1) (Nat.succ_pos n)
        (D.geometricFiber X₀).left
        ((scalarReductionDerivedExtension l E (D.geometricFiber X₀).left n).obj L.obj))
      (f : K ⟶ L)
      (P Q : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory)
      (e : DerivedCategory.Q.obj P.obj ≅ K.obj)
      (d : DerivedCategory.Q.obj Q.obj ≅ L.obj),
      ((integralFibreLarge D l E (localExtensionPoint D X₀ m hm y)).map f ≫
        integralTransport D l hl E X₀ m hm y L Q d =
      integralTransport D l hl E X₀ m hm y K P e ≫
        (integralFibreLarge D l E
          (localExtensionPoint D X₀ m hm y ≫
            (End.of (D.geometricGaloisFrobenius X₀)) ^ m)).map f) ∧
      ∀ (v : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
        (_hv : v = localExtensionPoint D X₀ m hm y ∨
          v = localExtensionPoint D X₀ m hm y ≫
            (End.of (D.geometricGaloisFrobenius X₀)) ^ m) (n : ℕ),
        (pointReductionModuleTensor l E n).map
            ((integralFibreLarge D l E v).map f) ≫
          (reduction D l hl E v L Q d n).hom =
        (reduction D l hl E v K P e n).hom ≫
          (finiteFibre D l E v n).map
            ((scalarReductionDerivedExtension l E (D.geometricFiber X₀).left n).map f.hom))

/-- Completed stalk transport reduces to the specified finite normalized transport,
with the canonical identifications, all quotient transitions, and all integral morphisms.

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (4)
(blueprint: lem-trf-completed-stalk-frobenius-reduction).

Proof:
1. Integral pullback preservation and point-sections reduction give reduction. Its
   factors are the projection-adjoint pullback map and the unit-normalized sections map.
2. Finite fixed-point composition commutes with quotient scalar extension. The
   scheme/Galois coefficient-coherence square then gives the same square for tau_n.
   Finite point sections commute with these quotients, including their cocycles.
3. Completed pullback is the specified Roos realization. Integral pullback composition
   identifies the target with pullback along ybar followed by g^m. Exact sections carry
   the two product components and the differential 1-transition to the same module
   Roos complex. The existing integralNormalized realizes the whole finite tower map.
4. Normalized DVR effectivity and the evaluation calculus identify each reduction
   with the scalar-extension adjunct of the actual limit projection. Point reduction
   unit normalization identifies its sections comparison with the same adjunct.
5. Transpose q_n tau = tau_n p_n through the actual coefficient adjunction. Naturality
   in its source and target gives exactly the displayed finite reduction square.
6. Successive quotient normalization identifies successive tensor units with the
   direct unit. Transposing through that adjunction identifies quotient coherence
   with the reductionAdjoint equations below. These use every a ≤ b, including a=b.
   Functorial quotients, natural kappa and the functorial whole Roos map give naturality
   in all derived integral morphisms, independently of the chosen good representatives.
-/
theorem completedStalkFrobeniusReduction
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) :
    ReductionStatement D l hl E X₀ m hm y := by
  sorry

end WeilConjectures.CompletedStalkFrobenius
