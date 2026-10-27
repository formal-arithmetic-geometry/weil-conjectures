module

public import Sheaf.Paper.PairingData
public import Sheaf.Paper.DerivedPullbackTensorIso

/-! # Mixed-support cup product and the support-order convention

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
Mixed-support cup product (blueprint: def-pod-mixed-support-cup-product).
The left-support maps are the existing coefficient-valued pairing cups.
The signed swaps use the definition owners def-pur-finite-pullback-tensor-comparison,
def-pod-integral-tensor-constraints and def-sf-rational-common-tensor-symmetries.
The right-support maps exchange the two source factors and then apply compact
support to the signed tensor symmetry on X. No coherence property is asserted here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.SixFunctorDatum

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {m : ℕ}

/-- Right-support finite cup: swap coefficient complexes, apply the existing
left-support cup, and apply compact support to the canonical signed site symmetry.
The target-coordinate maps identify exactly the datum's normalized tensor.
Source: support-order display (blueprint: def-pod-mixed-support-cup-product). -/
def finiteRightSupportCup (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K L : finiteTorConstructibleCategory C.l E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left) :=
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E (m + 1)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let F := Functor.mapDerivedCategory.{u + 2, u + 1, u + 1, u + 1, u + 2, u + 2}
    (pointFiniteSections D.k (Padic.coefficientExtensionRing C.l E (m + 1)))
  let b := (pullbackTensorBraiding (ProEt.topology X.obj.left)
    (integralCoefficientCommRingSheaf C.l E X.obj.left m)
    (finiteIntrinsicClosed C.l E X.obj.left m)
    (finiteIntrinsicTensorModels C.l E X.obj.left m)).hom.app (K.obj, L.obj)
  let t := eqToHom (S.finiteTensorNormalization X K L) ≫ b ≫
    eqToHom (S.finiteTensorNormalization X L K).symm
  ((pointModuleDerivedBraiding
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E (m + 1)))).braiding _ _).hom ≫
    finitePairingCup S X c K L ≫ F.map
      ((S.finite.support (sixFunctorStructure X) c).map
        (ObjectProperty.homMk
          (X := pairingFiniteInput X (((S.finiteTensorDomainStage X).obj K).obj L))
          (Y := pairingFiniteInput X (((S.finiteTensorDomainStage X).obj L).obj K)) t)).hom

/-- Right-support completed cup, using the recorded reduction-normalized integral
Koszul symmetry, with the same completed support functor as the left-support cup.
Source: support-order display (blueprint: def-pod-mixed-support-cup-product). -/
def integralRightSupportCup (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K L : (finiteTorConstructibleIntegral C.l E X.obj.left).FullSubcategory) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers C.l E))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let b := (pullbackTensorIntegralBraiding C.l E X.obj.left
    (pairingIntegralInput X K) (pairingIntegralInput X L)).hom
  let h := S.higher.integralTensorNormalization X
  let t := eqToHom (congrArg (fun T ↦ ((T.obj (pairingIntegralInput X K)).obj
    (pairingIntegralInput X L))) h) ≫ b ≫
    eqToHom (congrArg (fun T ↦ ((T.obj (pairingIntegralInput X L)).obj
      (pairingIntegralInput X K))) h).symm
  ((pointModuleDerivedBraiding
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers C.l E))).braiding _ _).hom ≫
    integralPairingCup S X c K L ≫
      (pointFibreIntegralAmbient D C.l E).map
        (((S.higher.integral.support (sixFunctorStructure X) c).map t).hom)

/-- Right-support rational cup, using the localization of the integral signed swap.
Source: support-order display (blueprint: def-pod-mixed-support-cup-product). -/
def rationalRightSupportCup (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K L : sfRationalConstructibleCategory C.l E X.obj.left) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  letI : HasDerivedCategory.{u} (ModuleCat.{u} E) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let h := S.higher.rationalTensorNormalization X
  let t := eqToHom (congrArg (fun T ↦ (T.obj K).obj L) h) ≫
    (pullbackTensorRationalBraiding C.l E X.obj.left K L).hom ≫
      eqToHom (congrArg (fun T ↦ (T.obj L).obj K) h).symm
  ((pointModuleDerivedBraiding E).braiding _ _).hom ≫
    rationalPairingCup S X c K L ≫
      (pointRationalFibre D C.l C.different E ⋙ (DerivedCategory.pointFiniteDimensional E).ι).map
        ((S.higher.rational.support (sixFunctorStructure X) c).map t)

/-- Right-support algebraically closed cup with the common finite-stage symmetry class.
Source: support-order display (blueprint: def-pod-mixed-support-cup-product). -/
def commonRightSupportCup (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (X : SixFunctorSpace D)
    [IsSeparated X.obj.hom]
    (c : Compactification (sixFunctorStructure X).hom.left)
    (K L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  letI : HasDerivedCategory.{u} (ModuleCat.{u} C.Qbar) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let h := S.closure.commonStageTensorNormalization X
  let t := eqToHom (congrArg (fun T ↦ (T.obj K).obj L) h) ≫
    (pullbackTensorCommonBraiding C.l C.Qbar X.obj.left K L).hom ≫
      eqToHom (congrArg (fun T ↦ (T.obj L).obj K) h).symm
  ((pointModuleDerivedBraiding C.Qbar).braiding _ _).hom ≫
    commonPairingCup S X c K L ≫
      (pointQbarFibre D C.l C.different C.Qbar ⋙
        DerivedCategory.pointFdQbarRealization C.l C.Qbar).map
          ((S.closure.commonStage.support (sixFunctorStructure X) c).map t)

/-- The four existing left-support products and their right-support counterparts
on the fixed smooth separated geometrically connected finite-type geometric fibre.
Positive exponents are written m+1. Compactification is the construction parameter
for support; neither properness nor an ambient exceptional-adjoint datum is required.
Source: all defining displays (blueprint: def-pod-mixed-support-cup-product). -/
def poincareMixedSupportCupProducts (S : SixFunctorDatum D C E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m))) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d)
    (c : Compactification (G.structureMorphism D.k)) :=
  let X := pairingGeometricSpace D d G
  letI : IsSeparated X.obj.hom := by
    change IsSeparated (G.structureMorphism D.k)
    dsimp [PoincareDualitySetting.structureMorphism]
    infer_instance
  (finitePairingCup S X c, integralPairingCup S X c,
    rationalPairingCup S X c, commonPairingCup S X c,
    finiteRightSupportCup S X c, integralRightSupportCup S X c,
    rationalRightSupportCup S X c, commonRightSupportCup S X c)

end WeilConjectures.SixFunctorDatum
