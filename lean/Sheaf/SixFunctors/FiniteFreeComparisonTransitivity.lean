/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.SixFunctors.FiniteFreeImageComparison
public import Sheaf.Paper.ExceptionalCoefficientMaps
public import Sheaf.SixFunctors.EtaleHomComparisonModels
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Paper.DualityPairing
public import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange
import Sheaf.Paper.FiniteFreeScalarExtension
import Sheaf.CategoryTheory.FlatScalarTowerCoherence
import Sheaf.Paper.ToposScalarMateTransitivity
import Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeTensor
import Sheaf.Algebra.Homology.ScalarHomTensorCoherence
import Sheaf.Algebra.Homology.ScalarHomComparisonTower

/-! # Transitivity of the five finite-free coefficient comparisons

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraph 3
(blueprint: lem-sf-finite-free-comparison-transitivity).

The canonical scalar functors, their balanced associators, the direct-image mate,
and the normalized tensor/unit comparisons are reused. The component constructions
below specialize the counit and evaluation transposes to this node's fixed
compactification and arbitrary presentations of its ambient right adjoints.
`TowerLaws` and `IdentityLaws` display all five equations without suppressing
variance or endpoint transports. No free basis is selected by a construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

namespace FiniteFreeComparison

/-- Restriction along the identity acts identically on sections.
Source: blueprint finite-free-extension proof, paragraph 3
(blueprint: lem-sf-finite-free-comparison-transitivity). -/
def restrictionId (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Sheaf.restrictScalars X.smallEtaleTopology (RingHom.id A) ≅
      𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  NatIso.ofComponents (fun M ↦
    (fullyFaithfulSheafToPresheaf X.smallEtaleTopology _).preimageIso
      (Functor.isoWhiskerLeft M.obj (ModuleCat.restrictScalarsId A) ≪≫
        Functor.rightUnitor M.obj)) (fun {M N} f ↦
    (fullyFaithfulSheafToPresheaf X.smallEtaleTopology _).map_injective (by
      ext U : 2
      rfl))

/-- The scalar identity unitor, conjugate to identity restriction of scalars.
Source: blueprint finite-free-extension proof, paragraph 3
(blueprint: lem-sf-finite-free-comparison-transitivity). -/
def scalarId (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    scalarExtension (RingHom.id A) X ≅ 𝟭 (DerivedCategoryModule A X) :=
  Adjunction.leftAdjointIdIso
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology (RingHom.id A)))
    (Functor.mapDerivedCategoryNatIso (restrictionId A X) ≪≫
      Functor.mapDerivedCategoryIdIso _)

/-- Inverse of the specified direct-image coefficient map on its isomorphism domain.
The zero extension makes the construction total; finite freeness guarantees that
only the inverse branch occurs in the theorem below.
Source: blueprint finite-free-extension proof, paragraphs 1 and 3
(blueprint: lem-sf-finite-free-comparison-transitivity). -/
def imageInverse {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X)
    (K : DerivedCategoryModule A Z) :
    (R(lowerStar (ModuleCat.{u + 1} B) i)).obj ((scalarExtension φ Z).obj K) ⟶
      (scalarExtension φ X).obj ((R(lowerStar (ModuleCat.{u + 1} A) i)).obj K) :=
  open Classical in
  if h : IsIso ((scalarMate φ i).app K) then
    @inv _ _ _ _ ((scalarMate φ i).app K) h else 0

/-- The closed exceptional comparison is the transpose of the inverse closed
image comparison followed by the scalar-extended exceptional counit.
The adjunctions are presentations of the ordinary ambient right adjoints.
Source: blueprint finite-free-extension proof, paragraph 3
(blueprint: lem-sf-finite-free-comparison-transitivity). -/
def closedMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X)
    {GA : DerivedCategoryModule A X ⥤ DerivedCategoryModule A Z}
    {GB : DerivedCategoryModule B X ⥤ DerivedCategoryModule B Z}
    (adA : R(lowerStar (ModuleCat.{u + 1} A) i) ⊣ GA)
    (adB : R(lowerStar (ModuleCat.{u + 1} B) i) ⊣ GB)
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Z).obj (GA.obj M) ⟶ GB.obj ((scalarExtension φ X).obj M) :=
  adB.homEquiv _ _ (imageInverse φ i (GA.obj M) ≫
    (scalarExtension φ X).map (adA.counit.app M))

/-- Inverse of the fixed compact-support comparison, assembled from proper
projection followed by open extension by zero. The zero branch is outside
its finite-free isomorphism domain.
Source: blueprint finite-free-extension proof, paragraph 3
(blueprint: lem-sf-finite-free-comparison-transitivity). -/
def compactInverse {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X S : Scheme.{u}} {a : X ⟶ S} (c : Compactification a)
    (K : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((scalarExtension φ X).obj K) ⟶
      (scalarExtension φ S).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) :=
  open Classical in
  if h : IsIso ((finiteFreeCompactImageMap φ c).app K) then
    @inv _ _ _ _ ((finiteFreeCompactImageMap φ c).app K) h else 0

/-- The structure exceptional coefficient comparison at an arbitrary base object.
Source: blueprint finite-free-extension proof, paragraph 3
(blueprint: lem-sf-finite-free-comparison-transitivity). -/
def compactRightMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X S : Scheme.{u}} {a : X ⟶ S} (c : Compactification a)
    {GA : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X}
    {GB : DerivedCategoryModule B S ⥤ DerivedCategoryModule B X}
    (adA : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ GA)
    (adB : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ GB)
    (N : DerivedCategoryModule A S) :
    (scalarExtension φ X).obj (GA.obj N) ⟶ GB.obj ((scalarExtension φ S).obj N) :=
  adB.homEquiv _ _ (compactInverse φ c (GA.obj N) ≫
    (scalarExtension φ S).map (adA.counit.app N))

/-- The dualizing comparison evaluates the compact-support counit transpose
at the coefficient unit and applies its canonical scalar unit identification.
Source: blueprint finite-free-extension proof, paragraph 3
(blueprint: lem-sf-finite-free-comparison-transitivity). -/
def dualizingMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X S : Scheme.{u}} {a : X ⟶ S} (c : Compactification a)
    {GA : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X}
    {GB : DerivedCategoryModule B S ⥤ DerivedCategoryModule B X}
    (adA : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ GA)
    (adB : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ GB) :
    (scalarExtension φ X).obj (GA.obj (𝟙_ (DerivedCategoryModule A S))) ⟶
      GB.obj (𝟙_ (DerivedCategoryModule B S)) :=
  compactRightMap φ c adA adB (𝟙_ _) ≫ GB.map (ExceptionalCoefficients.unitIso φ S).hom

/-- The evaluation-transpose internal-Hom comparison, on arbitrary unbounded inputs.
Source: blueprint finite-free-extension proof, paragraphs 2 and 3
(blueprint: lem-sf-finite-free-comparison-transitivity). -/
def homMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (K M : DerivedCategoryModule A X) :
    (scalarExtension φ X).obj (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ⟶
      ((derivedHom (ModuleCat.{u + 1} B) X).obj
        (op ((scalarExtension φ X).obj K))).obj ((scalarExtension φ X).obj M) :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} B)
    ((scalarExtension φ X).obj K)).homEquiv _ _
      ((etaleHomTensorComparison X φ K
        (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M)).hom ≫
          (scalarExtension φ X).map
            ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K).counit.app M))

/-- Verdier comparison: extended-evaluation transpose followed by Hom of u.
Source: blueprint finite-free-extension proof, paragraphs 2 and 3
(blueprint: lem-sf-finite-free-comparison-transitivity). -/
def verdierMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X S : Scheme.{u}} {a : X ⟶ S} (c : Compactification a)
    {GA : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X}
    {GB : DerivedCategoryModule B S ⥤ DerivedCategoryModule B X}
    (adA : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ GA)
    (adB : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ GB)
    (K : DerivedCategoryModule A X) :
    (scalarExtension φ X).obj (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj
        (GA.obj (𝟙_ (DerivedCategoryModule A S)))) ⟶
      ((derivedHom (ModuleCat.{u + 1} B) X).obj
        (op ((scalarExtension φ X).obj K))).obj (GB.obj (𝟙_ (DerivedCategoryModule B S))) :=
  homMap φ X K (GA.obj (𝟙_ _)) ≫
    ((derivedHom (ModuleCat.{u + 1} B) X).obj
      (op ((scalarExtension φ X).obj K))).map (dualizingMap φ c adA adB)

/-- The five coefficient-tower equations with all scalar associators and Hom
variance transports displayed. The fields also identify the common transposes.
All functors and arrows are the published constructions or the specialized
counit/evaluation constructions above; no comparison arrow is supplied as data.
Source: blueprint finite-free-extension proof, paragraph 3
(blueprint: lem-sf-finite-free-comparison-transitivity). -/
structure TowerLaws
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C)
    {V X Z S : Scheme.{u}} (f : V ⟶ X) (i : Z ⟶ X)
    {a : X ⟶ S} (c : Compactification a)
    {GA : DerivedCategoryModule A X ⥤ DerivedCategoryModule A Z}
    {GB : DerivedCategoryModule B X ⥤ DerivedCategoryModule B Z}
    {GC : DerivedCategoryModule C X ⥤ DerivedCategoryModule C Z}
    (adA : R(lowerStar (ModuleCat.{u + 1} A) i) ⊣ GA)
    (adB : R(lowerStar (ModuleCat.{u + 1} B) i) ⊣ GB)
    (adC : R(lowerStar (ModuleCat.{u + 1} C) i) ⊣ GC)
    {WA : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X}
    {WB : DerivedCategoryModule B S ⥤ DerivedCategoryModule B X}
    {WC : DerivedCategoryModule C S ⥤ DerivedCategoryModule C X}
    (awA : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ WA)
    (awB : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ WB)
    (awC : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c ⊣ WC) : Prop where
  image_comp : ∀ K : DerivedCategoryModule A V,
    (scalarExtension ψ X).map ((scalarMate φ f).app K) ≫
        (scalarMate ψ f).app ((scalarExtension φ V).obj K) ≫
        R(lowerStar (ModuleCat.{u + 1} C) f).map
          ((ProEtale.pbcFixedScalarExtensionComp V.smallEtaleTopology φ ψ
            (ψ.comp φ) rfl).hom.app K) =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).hom.app ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫
        (scalarMate (ψ.comp φ) f).app K
  closed_comp : ∀ M : DerivedCategoryModule A X,
    (scalarExtension ψ Z).map (closedMap φ i adA adB M) ≫
        closedMap ψ i adB adC ((scalarExtension φ X).obj M) ≫
        GC.map ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).hom.app M) =
      (ProEtale.pbcFixedScalarExtensionComp Z.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).hom.app (GA.obj M) ≫ closedMap (ψ.comp φ) i adA adC M
  dualizing_comp :
    (scalarExtension ψ X).map (dualizingMap φ c awA awB) ≫ dualizingMap ψ c awB awC =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).hom.app (WA.obj (𝟙_ (DerivedCategoryModule A S))) ≫
        dualizingMap (ψ.comp φ) c awA awC
  hom_comp : ∀ K M : DerivedCategoryModule A X,
    (scalarExtension ψ X).map (homMap φ X K M) ≫
        homMap ψ X ((scalarExtension φ X).obj K) ((scalarExtension φ X).obj M) ≫
        ((derivedHom (ModuleCat.{u + 1} C) X).map
          ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
            (ψ.comp φ) rfl).inv.app K).op).app
              ((scalarExtension ψ X).obj ((scalarExtension φ X).obj M)) ≫
        ((derivedHom (ModuleCat.{u + 1} C) X).obj
          (op ((scalarExtension (ψ.comp φ) X).obj K))).map
            ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
              (ψ.comp φ) rfl).hom.app M) =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).hom.app
            (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M) ≫
        homMap (ψ.comp φ) X K M
  verdier_comp : ∀ K : DerivedCategoryModule A X,
    (scalarExtension ψ X).map (verdierMap φ c awA awB K) ≫
        verdierMap ψ c awB awC ((scalarExtension φ X).obj K) ≫
        ((derivedHom (ModuleCat.{u + 1} C) X).map
          ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
            (ψ.comp φ) rfl).inv.app K).op).app
              (WC.obj (𝟙_ (DerivedCategoryModule C S))) =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).hom.app
            (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj
              (WA.obj (𝟙_ (DerivedCategoryModule A S)))) ≫
        verdierMap (ψ.comp φ) c awA awC K
  image_transpose : ∀ K : DerivedCategoryModule A V,
    L(upperStar (ModuleCat.{u + 1} C) f).map ((scalarMate (ψ.comp φ) f).app K) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} C) f).counit.app
          ((scalarExtension (ψ.comp φ) V).obj K) =
      (scalarPullbackIso (ψ.comp φ) f).hom.app
          ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫
        (scalarExtension (ψ.comp φ) V).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app K)
  closed_transpose : ∀ M : DerivedCategoryModule A X,
    (adC.homEquiv _ _).symm (closedMap (ψ.comp φ) i adA adC M) =
      imageInverse (ψ.comp φ) i (GA.obj M) ≫
        (scalarExtension (ψ.comp φ) X).map (adA.counit.app M)
  dualizing_transpose :
    (awC.homEquiv _ _).symm (dualizingMap (ψ.comp φ) c awA awC) =
      compactInverse (ψ.comp φ) c (WA.obj (𝟙_ (DerivedCategoryModule A S))) ≫
        (scalarExtension (ψ.comp φ) S).map
          (awA.counit.app (𝟙_ (DerivedCategoryModule A S))) ≫
        (ExceptionalCoefficients.unitIso (ψ.comp φ) S).hom
  hom_transpose : ∀ K M : DerivedCategoryModule A X,
    ((derivedTensorHomAdjunction (ModuleCat.{u + 1} C)
        ((scalarExtension (ψ.comp φ) X).obj K)).homEquiv _ _).symm
          (homMap (ψ.comp φ) X K M) =
      (etaleHomTensorComparison X (ψ.comp φ) K
          (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M)).hom ≫
        (scalarExtension (ψ.comp φ) X).map
          ((derivedTensorHomAdjunction (ModuleCat.{u + 1} A) K).counit.app M)

/-- Identity-extension equations for the same five specified maps, with the
scalar identity unitor and the contravariant Hom transport retained.
Source: blueprint finite-free-extension proof, paragraph 3
(blueprint: lem-sf-finite-free-comparison-transitivity). -/
structure IdentityLaws
    (A : Type (u + 1)) [CommRing A]
    {V X Z S : Scheme.{u}} (f : V ⟶ X) (i : Z ⟶ X)
    {a : X ⟶ S} (c : Compactification a)
    {GA : DerivedCategoryModule A X ⥤ DerivedCategoryModule A Z}
    (adA : R(lowerStar (ModuleCat.{u + 1} A) i) ⊣ GA)
    {WA : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X}
    (awA : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ WA) :
    Prop where
  image_id : ∀ K : DerivedCategoryModule A V,
    (scalarMate (RingHom.id A) f).app K ≫
        R(lowerStar (ModuleCat.{u + 1} A) f).map ((scalarId A V).hom.app K) =
      (scalarId A X).hom.app ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K)
  closed_id : ∀ M : DerivedCategoryModule A X,
    closedMap (RingHom.id A) i adA adA M ≫ GA.map ((scalarId A X).hom.app M) =
      (scalarId A Z).hom.app (GA.obj M)
  dualizing_id : dualizingMap (RingHom.id A) c awA awA =
    (scalarId A X).hom.app (WA.obj (𝟙_ (DerivedCategoryModule A S)))
  hom_id : ∀ K M : DerivedCategoryModule A X,
    homMap (RingHom.id A) X K M ≫
        ((derivedHom (ModuleCat.{u + 1} A) X).map ((scalarId A X).inv.app K).op).app
          ((scalarExtension (RingHom.id A) X).obj M) ≫
        ((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).map ((scalarId A X).hom.app M) =
      (scalarId A X).hom.app (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj M)
  verdier_id : ∀ K : DerivedCategoryModule A X,
    verdierMap (RingHom.id A) c awA awA K ≫
        ((derivedHom (ModuleCat.{u + 1} A) X).map ((scalarId A X).inv.app K).op).app
          (WA.obj (𝟙_ (DerivedCategoryModule A S))) =
      (scalarId A X).hom.app (((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj
        (WA.obj (𝟙_ (DerivedCategoryModule A S))))

end FiniteFreeComparison

/-- The five specified finite-free coefficient comparisons compose canonically,
including their identity equations and their actual counit/evaluation transposes.
The right adjoints are quantified together with their adjunctions to the specified
ordinary closed image and fixed-compactification functors. Thus the assertion is
independent of the presentation of an adjoint, as well as of temporary free bases.
There is no boundedness, constructibility or perfectness hypothesis on an input.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraph 3
(blueprint: lem-sf-finite-free-comparison-transitivity).

Proof:
1. Expand a B/A basis and then a C/B basis to obtain a C/A basis. The finite-free
scalar-coordinate theorem (lem-pur-finite-free-scalar-extension) makes extension
an exact finite direct sum on all complexes, including unbounded complexes.
Derived change of rings (lem-pur-derived-change-of-rings) identifies this with
its K-flat model. The normalized flat tower associator
(lem-sfb-flat-scalar-tower-coherence) sends (m tensor b) tensor c to m tensor bc.
2. Apply lem-sfb-topos-scalar-mate-transitivity to ordinary etale inverse/direct
image. Its counit normalization gives image_comp and image_transpose. The finite
free image theorem (lem-sf-finite-free-image-comparison) makes these maps
invertible for i and for the proper part of the compactification.
3. Open extension has the identity coefficient map on the open and the zero map
off it. Its two tower composites therefore agree termwise. Paste this equality
with the proper comparison, using naturality, to obtain the compact-support
tower equality for finiteFreeCompactImageMap. Invert these canonical comparisons.
4. For the closed adjunction the mate definition (def-weil-pbc-adjunction-mate)
says epsilon_B F_B(b_a) = T_a(epsilon_A) c_a inverse. Transpose the composite
b_b T_b(b_a), move b_a through c_b inverse by naturality, and use the two counit
equations. The result is T_b T_a(epsilon_A) T_b(c_a inverse) c_b inverse.
The inverse tower equation and associator naturality give exactly the defining
transpose of b_ba. Injectivity of the adjunction bijection proves closed_comp;
this is also lem-weil-pbc-mate-pasting. It retains closed_transpose literally.
5. Repeat this calculation for the fixed compact-support adjunction, using its
inverse comparison from step 3. Evaluate at the coefficient unit. Naturality
moves the A-to-B unit identification through the B-to-C mate. The coefficient
unit maps compose by multiplication, giving dualizing_comp and its transpose.
6. Use the normalized tensor data of lem-sf-ringed-finite-free-tensor-data and
lem-sfb-scalar-hom-tensor-coherence in lem-pur-scalar-hom-comparison-tower.
The evaluation transpose is homMap, and the tower theorem gives hom_comp with
both endpoint transports, as well as hom_transpose, for arbitrary inputs.
7. Expand verdierMap as homMap followed by Hom of dualizingMap. Naturality in
the second Hom variable moves the first dualizingMap through the second
homMap. Combine the dualizing factors by step 5 and Hom factors by step 6.
This gives verdier_comp for the defined map, including its contravariant transport.
8. For identity coefficients the scalar unitor is conjugate to identity
restriction. The image comparison is the mate of an identity square; the
open coefficient map is identity termwise. Closed and compact-support mates
therefore transpose to their counits, whose adjuncts are identities. The Hom
tower theorem supplies hom_id. The definition of verdierMap gives verdier_id.
All equations compare specified transposes or normalized tensor maps. Bases
enter only the proof of exactness, so none of the maps or laws depends on them. -/
theorem finiteFreeComparisonTransitivity
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    {X V Z : Scheme.{u}}
    (aX : X ⟶ Spec (CommRingCat.of D.k))
    (aV : V ⟶ Spec (CommRingCat.of D.k))
    (aZ : Z ⟶ Spec (CommRingCat.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aV] [LocallyOfFiniteType aV] [QuasiCompact aV]
    [IsSeparated aZ] [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (f : V ⟶ X) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (c : Compactification aX)
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C] [Algebra A B] [Algebra B C]
    (_hA : ∃ n : ℕ, ((l ^ n : ℕ) : A) = 0)
    (_hB : ∃ n : ℕ, ((l ^ n : ℕ) : B) = 0)
    (_hC : ∃ n : ℕ, ((l ^ n : ℕ) : C) = 0)
    (_hAB : ∃ r : ℕ, Nonempty (Module.Basis (Fin r) A B))
    (_hBC : ∃ r : ℕ, Nonempty (Module.Basis (Fin r) B C))
    {GA : DerivedCategoryModule A X ⥤ DerivedCategoryModule A Z}
    {GB : DerivedCategoryModule B X ⥤ DerivedCategoryModule B Z}
    {GC : DerivedCategoryModule C X ⥤ DerivedCategoryModule C Z}
    (adA : R(lowerStar (ModuleCat.{u + 1} A) i) ⊣ GA)
    (adB : R(lowerStar (ModuleCat.{u + 1} B) i) ⊣ GB)
    (adC : R(lowerStar (ModuleCat.{u + 1} C) i) ⊣ GC)
    {WA : DerivedCategoryModule A (Spec (CommRingCat.of D.k)) ⥤
      DerivedCategoryModule A X}
    {WB : DerivedCategoryModule B (Spec (CommRingCat.of D.k)) ⥤
      DerivedCategoryModule B X}
    {WC : DerivedCategoryModule C (Spec (CommRingCat.of D.k)) ⥤
      DerivedCategoryModule C X}
    (awA : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ WA)
    (awB : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ WB)
    (awC : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c ⊣ WC) :
    FiniteFreeComparison.TowerLaws (algebraMap A B) (algebraMap B C) f i c
        adA adB adC awA awB awC ∧
      FiniteFreeComparison.IdentityLaws A f i c adA awA ∧
      FiniteFreeComparison.IdentityLaws B f i c adB awB ∧
      FiniteFreeComparison.IdentityLaws C f i c adC awC := by
  sorry

end AlgebraicGeometry.Etale
