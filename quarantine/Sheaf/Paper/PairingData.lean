/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module
public import Sheaf.Paper.ConstructibleProjectionMates
public import WeilConjectures.AlgebraicGeometry.PoincareDualitySetting
public import Sheaf.Paper.SixFunctorOrientation
public import Sheaf.Paper.PointFibreDerivedTensor
public import Sheaf.Paper.PairingFiniteTensorTransport
public import Sheaf.Paper.PairingCoefficientUnit
/-! # Pairing data for smooth Poincare duality
Source: main-20261015, sec-poincare-duality/sk-def-pairing-data/_section.md,
both displayed composites (blueprint: sk-def-pairing-data).
The coefficient-complex maps apply the canonical inverse point tensorator and
point unit map to the selected operations' projection and counit composites.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The canonical tensor and coefficient-unit identifications used when reading the
following point images in coefficient complexes. The theorem fixes their values
on K-flat representatives, quotient transitions and common finite stages.
Source: the passage through Fib_s (blueprint: sk-def-pairing-data). -/
def pairingPointIdentifications (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum) :=
  (⟨(pointFibreDerivedTensor D C.l C.different C.Qbar).choose,
    (pointFibreDerivedTensor D C.l C.different C.Qbar).choose_spec⟩ :
    {T : PointFibreDerivedTensorSystem D C.l C.different C.Qbar //
      Nonempty (PointFibreDerivedTensorCanonical D C.l C.different C.Qbar T)})

/-- The fixed geometric fibre in the existing finite-type over-category.
No new geometric setting is introduced.
Source: the fixed X_0 and its base change (blueprint: sk-def-pairing-data). -/
def pairingGeometricSpace (D : FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) : SixFunctorSpace D :=
  ⟨Over.mk (G.structureMorphism D.k),
    ⟨by
      dsimp [PoincareDualitySetting.structureMorphism]
      infer_instance,
      by
      dsimp [PoincareDualitySetting.structureMorphism]
      infer_instance⟩⟩

/-- Projection for the actual stage followed by its pull/direct counit.
Source: first displayed composite (blueprint: sk-def-pairing-data). -/
def pairingStageCup {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (A : SixFunctorExchangeData S T Q)
    (K L : B Q.X) :
    ((T Q.Y).obj ((S.support Q.f Q.compactification).obj K)).obj
      ((S.direct Q.f).obj L) ⟶
    (S.support Q.f Q.compactification).obj (((T Q.X).obj K).obj L) :=
  A.projectionComponent K ((S.direct Q.f).obj L) ≫
    (S.support Q.f Q.compactification).map
      (((T Q.X).obj K).map ((S.pullDirectAdjunction Q.f).counit.app L))

namespace SixFunctorDatum
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {m : ℕ}

/-- Forget finite Tor but retain bounded constructibility.
Source: the input categories (blueprint: sk-def-pairing-data). -/
def pairingFiniteInput (X : SixFunctorSpace D)
    (K : finiteTorConstructibleCategory C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left) :
    sixFunctorFiniteCategory D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) X :=
  ⟨K.obj, K.property.1⟩

/-- Integral finite-Tor objects in the constructible operation category.
Source: the completed input category (blueprint: sk-def-pairing-data). -/
def pairingIntegralInput (X : SixFunctorSpace D)
    (K : (finiteTorConstructibleIntegral C.l E X.obj.left).FullSubcategory) :
    sfIntegralConstructibleCategory C.l E X.obj.left := ⟨K.obj, K.property.1⟩

/-- Compact support at the point belongs to the precise finite-Tor source of
its canonical tensor comparison. Source: RΓ_c (blueprint: sk-def-pairing-data). -/
def pairingFiniteSupport (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K : finiteTorConstructibleCategory C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left) :
    finiteTorConstructibleCategory C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) (sixFunctorPoint D).obj.left :=
  ⟨((S.finite.support (sixFunctorStructure X) c).obj (pairingFiniteInput X K)).obj,
    S.finiteCoherence.supportDomain (sixFunctorStructure X) c
      (pairingFiniteInput X K) K.property⟩

/-- Ordinary direct image at the point, with its finite-Tor membership.
Source: RΓ (blueprint: sk-def-pairing-data). -/
def pairingFiniteDirect (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (L : finiteTorConstructibleCategory C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left) :
    finiteTorConstructibleCategory C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) (sixFunctorPoint D).obj.left :=
  letI : IsSeparated (sixFunctorStructure X).hom.left :=
    inferInstanceAs (IsSeparated X.obj.hom)
  ⟨((S.finite.direct (sixFunctorStructure X)).obj (pairingFiniteInput X L)).obj,
    S.finiteCoherence.directDomain (sixFunctorStructure X)
      (pairingFiniteInput X L) L.property⟩

/-- Completed compact support in the point tensorator's finite-Tor domain.
Source: RΓ_c (blueprint: sk-def-pairing-data). -/
def pairingIntegralSupport (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K : (finiteTorConstructibleIntegral C.l E X.obj.left).FullSubcategory) :
    (finiteTorConstructibleIntegral C.l E (sixFunctorPoint D).obj.left).FullSubcategory :=
  ⟨((S.higher.integral.support (sixFunctorStructure X) c).obj
      (pairingIntegralInput X K)).obj,
    S.integralCoherence.supportDomain (sixFunctorStructure X) c
      (pairingIntegralInput X K) K.property⟩

/-- Completed ordinary sections in the point tensorator's finite-Tor domain.
Source: RΓ (blueprint: sk-def-pairing-data). -/
def pairingIntegralDirect (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (L : (finiteTorConstructibleIntegral C.l E X.obj.left).FullSubcategory) :
    (finiteTorConstructibleIntegral C.l E (sixFunctorPoint D).obj.left).FullSubcategory :=
  letI : IsSeparated (sixFunctorStructure X).hom.left :=
    inferInstanceAs (IsSeparated X.obj.hom)
  ⟨((S.higher.integral.direct (sixFunctorStructure X)).obj
      (pairingIntegralInput X L)).obj,
    S.integralCoherence.directDomain (sixFunctorStructure X)
      (pairingIntegralInput X L) L.property⟩

end SixFunctorDatum
end WeilConjectures


namespace WeilConjectures.SixFunctorDatum
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {m : ℕ}

/-- Cancel the realization counits in the normalized derived tensor comparison.
This is the comparison from the published projection tensor to the intrinsic
point tensor, on the actual input objects.
Source: coefficient realization in the cup display (blueprint: sk-def-pairing-data). -/
def pairingFiniteTensorCoordinates (X : SixFunctorSpace D)
    (K L : proEtaleDerivedCategory X.obj.left
      (Padic.coefficientExtensionRing C.l E (m + 1))) :=
  let R := pairingDerivedRealization C.l E X.obj.left m
  (pairingFiniteRealizationTensor C.l E X.obj.left m).app
      (R.inverse.obj K, R.inverse.obj L) ≪≫
    (finiteIntrinsicDerivedTensor C.l E X.obj.left m).mapIso
      (Iso.prod (R.counitIso.app K) (R.counitIso.app L))

/-- The tensor/counit step in the finite-Tor full subcategory, using the counit
of S itself. Source: second cup arrow (blueprint: sk-def-pairing-data). -/
def pairingFiniteCounit (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (L : finiteTorConstructibleCategory C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left) :
    (CompactSupportFiniteProjection.torPull
      S.toSixFunctorOperationDatum.toSixFunctorFiniteOperations
      (sixFunctorStructure X)).obj (pairingFiniteDirect S X L) ⟶ L :=
  ObjectProperty.homMk
    ((S.finite.pullDirectAdjunction (sixFunctorStructure X)).counit.app
      (pairingFiniteInput X L)).hom

/-- The finite cup in bounded constructible coordinates. The projection component
and both subsequent maps use S.finite, including its support and its adjunction.
Source: both site-level cup arrows (blueprint: sk-def-pairing-data). -/
def pairingFiniteSiteCup (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K L : finiteTorConstructibleCategory C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left) :=
  CompactSupportFiniteProjection.component S.toSixFunctorOperationDatum.toSixFunctorFiniteOperations
      (sixFunctorStructure X) c (pairingFiniteInput X K) (pairingFiniteDirect S X L) ≫
    (S.finite.support (sixFunctorStructure X) c).map
      (((CompactSupportFiniteProjection.partialTensor
          S.toSixFunctorOperationDatum.toSixFunctorFiniteOperations X).obj
        (pairingFiniteInput X K)).map (pairingFiniteCounit S X L))

/-- Tensor coordinates at X identify the target with the recorded finite stage
T_X(K,L), with no replacement tensor.
Source: the cup's target (blueprint: sk-def-pairing-data). -/
def pairingFiniteTargetCoordinates (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    (K L : finiteTorConstructibleCategory C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left) :
    ((CompactSupportFiniteProjection.partialTensor
      S.toSixFunctorOperationDatum.toSixFunctorFiniteOperations X).obj
        (pairingFiniteInput X K)).obj L ≅
      pairingFiniteInput X (((S.finiteTensorDomainStage X).obj K).obj L) :=
  ObjectProperty.isoMk (intrinsicFiniteTorsionConstructible C.l E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left)
    (pairingFiniteTensorCoordinates X K.obj L.obj ≪≫
      eqToIso (S.finiteTensorNormalization X K L).symm)

/-- Finite mixed-support cup with the required coefficient-complex source.
The inverse canonical point tensorator is actually applied, then the normalized
finite tensor transport, then the projection/counit composite of S.finite.
Source: first displayed coefficient-valued arrow (blueprint: sk-def-pairing-data). -/
def finitePairingCup (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K L : finiteTorConstructibleCategory C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left) :=
  let T := (pairingPointIdentifications D C).val
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E (m + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let F := Functor.mapDerivedCategory.{u + 2, u + 1, u + 1, u + 1, u + 2, u + 2}
    (pointFiniteSections D.k (Padic.coefficientExtensionRing C.l E (m + 1)))
  ((T.finite E m).tensorIso (pairingFiniteSupport S X c K)
      (pairingFiniteDirect S X L)).inv ≫
    F.map (pairingFiniteTensorCoordinates (sixFunctorPoint D)
      (pairingFiniteSupport S X c K).obj (pairingFiniteDirect S X L).obj).inv ≫
    F.map (pairingFiniteSiteCup S X c K L).hom ≫
    F.map ((S.finite.support (sixFunctorStructure X) c).map
      (pairingFiniteTargetCoordinates S X K L).hom).hom

end WeilConjectures.SixFunctorDatum


namespace WeilConjectures.SixFunctorDatum
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {m : ℕ}

set_option maxHeartbeats 600000 in
-- Compare the stage tensor through its recorded normalization at the point.
/-- The completed cup has source RΓ_c(K) tensor RΓ(L). The tensorator is
applied to the actual finite-Tor support and direct-image objects. The intervening
equality is the operation datum's tensor normalization at s.
Source: first cup display, completed stage (blueprint: sk-def-pairing-data). -/
def integralPairingCup (S : SixFunctorDatum D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)))
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K L : (finiteTorConstructibleIntegral C.l E X.obj.left).FullSubcategory) :=
  letI : ∀ w : Spec (.of D.k), Invertible (C.l : (Spec (.of D.k)).residueField w) :=
    Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D C.l C.different)
  let T := (pairingPointIdentifications D C).val
  let A := (S.higher.integral.support (sixFunctorStructure X) c).obj
    (pairingIntegralInput X K)
  let B := (S.higher.integral.direct (sixFunctorStructure X)).obj (pairingIntegralInput X L)
  ((T.integral E).tensorIso (pairingIntegralSupport S X c K) (pairingIntegralDirect S X L)).inv ≫
    (pointFibreIntegralAmbient D C.l E).map
      (eqToHom (congrArg (fun H ↦ (((H.obj A).obj B).obj))
        (S.higher.integralTensorNormalization (sixFunctorPoint D))).symm) ≫
    (pointFibreIntegralAmbient D C.l E).map
      (pairingStageCup
        (S.higher.integralExchange (compactSupportProjectionSquare (sixFunctorStructure X) c))
        (pairingIntegralInput X K) (pairingIntegralInput X L)).hom


end WeilConjectures.SixFunctorDatum


namespace WeilConjectures.SixFunctorDatum
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {m : ℕ}

set_option maxHeartbeats 600000 in
-- Compare the stage tensor through its recorded normalization at the point.
/-- Rational cup with its actual tensor-of-cohomology source. All equalities
use the recorded tensor normalization; the projection and counit belong to S.
Source: first cup display, rational stage (blueprint: sk-def-pairing-data). -/
def rationalPairingCup (S : SixFunctorDatum D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)))
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K L : sfRationalConstructibleCategory C.l E X.obj.left) :=
  letI : ∀ w : Spec (.of D.k), Invertible (C.l : (Spec (.of D.k)).residueField w) :=
    Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D C.l C.different)
  let T := (pairingPointIdentifications D C).val
  let F := pointRationalFibre D C.l C.different E ⋙ (DerivedCategory.pointFiniteDimensional E).ι
  let A := (S.higher.rational.support (sixFunctorStructure X) c).obj K
  let B := (S.higher.rational.direct (sixFunctorStructure X)).obj L
  ((T.rational E).tensorIso A B).inv ≫ F.map
    (eqToHom (congrArg (fun H ↦ ((H.obj A).obj B))
      (S.higher.rationalTensorNormalization (sixFunctorPoint D))).symm) ≫
    F.map (pairingStageCup
      (S.higher.rationalExchange (compactSupportProjectionSquare (sixFunctorStructure X) c)) K L)


end WeilConjectures.SixFunctorDatum


namespace WeilConjectures.SixFunctorDatum
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {m : ℕ}

set_option maxHeartbeats 600000 in
-- Compare the stage tensor through its recorded normalization at the point.
/-- Algebraically closed cup, evaluated after the actual common-stage realization
and the canonical common-stage tensorator.
Source: first cup display, common stage (blueprint: sk-def-pairing-data). -/
def commonPairingCup (S : SixFunctorDatum D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)))
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left) :=
  letI : ∀ w : Spec (.of D.k), Invertible (C.l : (Spec (.of D.k)).residueField w) :=
    Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D C.l C.different)
  let T := (pairingPointIdentifications D C).val
  let F := pointQbarFibre D C.l C.different C.Qbar ⋙
    DerivedCategory.pointFdQbarRealization C.l C.Qbar
  let A := (S.closure.commonStage.support (sixFunctorStructure X) c).obj K
  let B := (S.closure.commonStage.direct (sixFunctorStructure X)).obj L
  (T.qbar.tensorIso A B).inv ≫ F.map
    (eqToHom (congrArg (fun H ↦ ((H.obj A).obj B))
      (S.closure.commonStageTensorNormalization (sixFunctorPoint D))).symm) ≫
    F.map (pairingStageCup
      (S.closure.commonStageExchange
        (compactSupportProjectionSquare (sixFunctorStructure X) c)) K L)


end WeilConjectures.SixFunctorDatum


namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : Type u) [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] (m : ℕ)

/-- Integral zero twist is the actual completed coefficient in degree zero.
Source: coefficient-unit convention (blueprint: sk-def-pairing-data). -/
def pairingIntegralZero :
    (sfOrientationIntegralLineOn D C E (sixFunctorPoint D) 0).obj ≅
      pointIntegralTensorUnit D C.l E := Iso.refl _

/-- Reduced zero twist is identified first by the root-quotient comparison,
then with the intrinsic tensor unit by its normalized scalar multiplication.
Source: finite coefficient-unit convention (blueprint: sk-def-pairing-data). -/
def pairingFiniteZero :
    (sfOrientationReducedLine D C E m (sixFunctorPoint D) 0).obj ≅
      (finiteIntrinsicClosed C.l E (Spec (.of D.k)) m).monoidal.tensorUnit :=
  letI := dlAdicGeometricResidueInvertible D C (sixFunctorPoint D).obj.left
  sfOrientationFiniteReduction C.l E (sixFunctorPoint D).obj.left m 0 ≪≫
    (pairingFiniteUnit C.l E (sixFunctorPoint D).obj.left m).symm

/-- Integral zero twist lifted to the very unit object chosen by the canonical
point tensor system. Source: point unit (blueprint: sk-def-pairing-data). -/
def pairingIntegralZeroInSystem :
    sfOrientationIntegralLineOn D C E (sixFunctorPoint D) 0 ≅
      (pointIntegralCtfToConstructible D C.l E).obj
        (((pairingPointIdentifications D C).val.integral E).monoidal.tensorUnit) :=
  ObjectProperty.isoMk _ (pairingIntegralZero D C E ≪≫
    eqToIso (((pairingPointIdentifications D C).val.integral E).unit_eq).symm)

/-- Rational zero twist is the localization of the same integral unit equality.
Source: rational coefficient convention (blueprint: sk-def-pairing-data). -/
def pairingRationalZero :
    (sfRationalConstructibleLocalization C.l E (Spec (.of D.k))).obj
      (sfOrientationIntegralLineOn D C E (sixFunctorPoint D) 0) ≅
    pointRationalTensorUnit D C.l C.different E
      ((pairingPointIdentifications D C).val.integral E) :=
  (sfRationalConstructibleLocalization C.l E (Spec (.of D.k))).mapIso
    (pairingIntegralZeroInSystem D C E)

/-- Common-stage zero twist uses the same base finite-extension inclusion
as the canonical point system. Source: common coefficient convention
(blueprint: sk-def-pairing-data). -/
def pairingCommonZero :=
  (GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := C.l) (Ω := C.Qbar) (Y := (sixFunctorPoint D).obj.left)
    (Padic.finiteCoefficientBase C.l C.Qbar)).mapIso
      (pairingRationalZero D C
        (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar
          (Padic.finiteCoefficientBase C.l C.Qbar)))

end WeilConjectures


namespace WeilConjectures

/-- Read a smooth orientation through the exceptional adjunction counit.
This auxiliary formula does not choose an orientation; the four specializations
below use the full, coherently normalized orientation datum.
Source: the second displayed composite (blueprint: sk-def-pairing-data). -/
def smoothTraceOfOrientation
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
    [∀ X, Category.{w} (B X)] {S : SixFunctorPushStage D B}
    {T : ∀ X, ℕ → B X} {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (d : ℕ)
    (γ : T X d ≅ (S.exceptional f c).obj (T Y 0)) :
    (S.support f c).obj (T X d) ⟶ T Y 0 :=
  (S.support f c).map γ.hom ≫ (S.exceptionalAdjunction f c).counit.app (T Y 0)

namespace SixFunctorDatum
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {m : ℕ}
  {S : SixFunctorDatum D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))}

/-- The finite smooth trace ends in the actual coefficient tensor unit.
The zero-twist quotient comparison is followed by unitIso.hom.
Source: normalized smooth trace (blueprint: sk-def-pairing-data). -/
def finiteNormalizedSmoothTrace (O : SfOrientationDatum S)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (d : ℕ) [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  letI : IsSeparated (sixFunctorStructure X).hom.left :=
    inferInstanceAs (IsSeparated X.obj.hom)
  let T := (pairingPointIdentifications D C).val
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E (m + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let F := Functor.mapDerivedCategory.{u + 2, u + 1, u + 1, u + 1, u + 2, u + 2}
    (pointFiniteSections D.k (Padic.coefficientExtensionRing C.l E (m + 1)))
  F.map (smoothTraceOfOrientation (sixFunctorStructure X) c d
      (SixFunctorOrientation O (sixFunctorStructure X) d c)).hom ≫
    F.map (pairingFiniteZero D C E m).hom ≫ (T.finite E m).unitIso.hom

/-- The completed smooth trace uses the completed coefficient-unit comparison.
Source: normalized smooth trace (blueprint: sk-def-pairing-data). -/
def integralNormalizedSmoothTrace (O : SfOrientationDatum S)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (d : ℕ) [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  letI : IsSeparated (sixFunctorStructure X).hom.left :=
    inferInstanceAs (IsSeparated X.obj.hom)
  let T := (pairingPointIdentifications D C).val
  let F := pointFibreIntegralAmbient D C.l E
  F.map (smoothTraceOfOrientation (sixFunctorStructure X) c d
      (SixFunctorOrientation.integralComponent O (sixFunctorStructure X) d c)).hom ≫
    F.map (pairingIntegralZero D C E).hom ≫ (T.integral E).unitIso.hom

/-- Rational trace with target the coefficient E in degree zero.
Source: normalized smooth trace (blueprint: sk-def-pairing-data). -/
def rationalNormalizedSmoothTrace (O : SfOrientationDatum S)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (d : ℕ) [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  letI : IsSeparated (sixFunctorStructure X).hom.left :=
    inferInstanceAs (IsSeparated X.obj.hom)
  let T := (pairingPointIdentifications D C).val
  let F := pointRationalFibre D C.l C.different E ⋙ (DerivedCategory.pointFiniteDimensional E).ι
  F.map ((S.higher.rational.support (sixFunctorStructure X) c).map
        (SixFunctorOrientation.rationalComponent O (sixFunctorStructure X) d c).hom ≫
      (S.higher.rational.exceptionalAdjunction (sixFunctorStructure X) c).counit.app _) ≫
    F.map (pairingRationalZero D C E).hom ≫ (T.rational E).unitIso.hom

/-- Common-stage trace with target the algebraically closed coefficient unit.
Its zero line is transported through the same base-stage inclusion as T.qbar.
Source: normalized smooth trace (blueprint: sk-def-pairing-data). -/
def commonNormalizedSmoothTrace (O : SfOrientationDatum S)
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (d : ℕ) [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
    (c : Compactification (sixFunctorStructure X).hom.left) :=
  letI : IsSeparated (sixFunctorStructure X).hom.left :=
    inferInstanceAs (IsSeparated X.obj.hom)
  let T := (pairingPointIdentifications D C).val
  let F := pointQbarFibre D C.l C.different C.Qbar ⋙
    DerivedCategory.pointFdQbarRealization C.l C.Qbar
  let B := Padic.finiteCoefficientBase C.l C.Qbar
  let R := T.rational (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar B)
  F.map ((S.closure.commonStage.support (sixFunctorStructure X) c).map
        (SixFunctorOrientation.commonComponent O (sixFunctorStructure X) d c).hom ≫
      (S.closure.commonStage.exceptionalAdjunction (sixFunctorStructure X) c).counit.app _) ≫
    F.map ((pairingCommonZero D C).hom ≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := C.l) (Ω := C.Qbar) (Y := (sixFunctorPoint D).obj.left) B).map
          (eqToHom R.unit_eq.symm)) ≫ T.qbar.unitIso.hom

end SixFunctorDatum
end WeilConjectures


namespace WeilConjectures.SixFunctorDatum
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {m : ℕ}
/-- Both defining arrows at every coefficient stage, as actual maps of coefficient complexes.
The geometric argument is exactly the fixed smooth separated geometrically
connected finite-type model, base changed from k_0 to k. Every cup applies
tensorIso.inv and every trace ends in unitIso.hom.
Source: both displayed definitions (blueprint: sk-def-pairing-data). -/
def pairingData (S : SixFunctorDatum D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m))) (O : SfOrientationDatum S)
    (d : ℕ) (G : PoincareDualitySetting D.k₀ d)
    (c : Compactification (G.structureMorphism D.k)) :=
  let X := pairingGeometricSpace D d G
  letI : IsSeparated X.obj.hom :=
    by
      change IsSeparated (G.structureMorphism D.k)
      dsimp [PoincareDualitySetting.structureMorphism]
      infer_instance
  letI : SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left :=
    by
      change SmoothOfRelativeDimension d (G.structureMorphism D.k)
      dsimp [PoincareDualitySetting.structureMorphism]
      infer_instance
  (finitePairingCup S X c, integralPairingCup S X c,
    rationalPairingCup S X c, commonPairingCup S X c,
    finiteNormalizedSmoothTrace O X d c, integralNormalizedSmoothTrace O X d c,
    rationalNormalizedSmoothTrace O X d c, commonNormalizedSmoothTrace O X d c,
    pairingPointIdentifications D C)

end WeilConjectures.SixFunctorDatum
