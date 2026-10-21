/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.PbcCompletedPullbackActual
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.ModulePullbackTensorIso

/-! # Canonical coefficient change and ringed pullback

The recorded arbitrary ringed-topos tensor/pullback interface is reexported.
The helpers retain its ordinary adjunction and K-flat normalization for the
completed coefficient structure maps, which need not be isomorphisms.
Source: Stacks Tags 03EL, 06YY, 0D6D and 099N
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B)
    (φY : pbcAdicCompletion Y dA ⟶ pbcAdicCompletion Y dB)
    (φX : pbcAdicCompletion X dA ⟶ pbcAdicCompletion X dB)

/-- Forget commutativity in a coefficient morphism without changing its ring map.
Source: Stacks Tag 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
abbrev pbcActualCoefficientRingMap (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) :=
  (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ

variable (hφ : pbcActualCoefficientRingMap Y φY ≫ pbcActualStructureMap g dB =
    pbcActualStructureMap g dA ≫
      (proEtaleSheafDirectImage g RingCat.{u + 1}).map (pbcActualCoefficientRingMap X φX))

include hφ in
/-- The two right-adjoint composites agree by the coefficient square, with identity
underlying section maps. Source: Stacks Tag 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: both composites evaluate a target module on the same base-changed site
object. Their actions agree by hφ. The identity function is therefore linear
and natural. These identity section functions specify the isomorphism uniquely. -/
theorem pbcActualScalarRightIso_exists :
    ∃! δ : pbcActualModulePush g dB ⋙
        SheafOfModules.restrictScalars.{u + 1} (pbcActualCoefficientRingMap Y φY) ≅
      SheafOfModules.restrictScalars.{u + 1} (pbcActualCoefficientRingMap X φX) ⋙
        pbcActualModulePush g dA,
      ∀ (N : pbcModules X (pbcAdicCompletion X dB)) (U : Y.ProEtᵒᵖ)
        (x : ((pbcActualModulePush g dB).obj N).val.obj U),
          (δ.hom.app N).val.app U x = x := by
  sorry

/-- The identity-on-sections right-adjoint comparison, retaining its coefficient square.
Source: Stacks Tag 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
def pbcActualScalarRightIso := (pbcActualScalarRightIso_exists g dA dB φY φX hφ).exists.choose

/-- The ordinary scalar/pullback comparison is the conjugate of the identity section
comparison under the actual tensor-unit-normalized adjunctions.
Source: Stacks Tag 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
def pbcActualScalarOrdinaryPullIso :
    pbcExtend φY ⋙ pbcActualModulePull g dB ≅
      pbcActualModulePull g dA ⋙ pbcExtend φX :=
  ((conjugateIsoEquiv
    ((pbcScalarAdjunction φY).comp
      (pbcActualModuleAdjunction g dB))
    ((pbcActualModuleAdjunction g dA).comp
        (pbcScalarAdjunction φX))).symm
      (pbcActualScalarRightIso g dA dB φY φX hφ)).symm

/-- The same canonical comparison on actual cochain complexes, degree by degree.
Source: Stacks Tag 0D6D
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
def pbcActualScalarOrdinaryPullComplexIso :
    (pbcExtend φY).mapHomologicalComplex (.up ℤ) ⋙
      (pbcActualModulePull g dB).mapHomologicalComplex (.up ℤ) ≅
    (pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ) ⋙
      (pbcExtend φX).mapHomologicalComplex (.up ℤ) :=
  letI : (pbcExtend φY).Additive := inferInstance
  letI : (pbcExtend φX).Additive := inferInstance
  letI : (pbcActualModulePull g dA).Additive := pbcActualModulePull_additive g dA
  letI : (pbcActualModulePull g dB).Additive := pbcActualModulePull_additive g dB
  Functor.mapHomologicalComplexCompIso
    (F := pbcExtend φY) (G := pbcActualModulePull g dB)
    (Iso.refl _) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (pbcActualScalarOrdinaryPullIso g dA dB φY φX hφ) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (F := pbcActualModulePull g dA) (G := pbcExtend φX)
        (Iso.refl _) (.up ℤ)).symm

/-- The derived scalar/pullback comparison retains the ordinary adjunction conjugate
on flat-term K-flat representatives. Source: Stacks Tags 06YY and 0D6D
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: scalar extension and ringed pullback preserve the flat-term K-flat resolving
class. On that class the two paths are identified by their invertible universal
counits and the ordinary adjunction conjugate above. The displayed equation is
that conjugation written without selecting inverse counits. It is natural on
resolving models and invariant under resolving quasi-isomorphisms. Descend it to
the derived localization. Every derived object has a resolving representative,
which proves invertibility and uniqueness of the resulting natural isomorphism. -/
theorem pbcActualScalarDerivedPullIso_exists :
    ∃! e : pbcDerivedExtend φY ⋙ pbcActualDerivedPull g dB ≅
        pbcActualDerivedPull g dA ⋙ pbcDerivedExtend φX,
      ∀ P : CochainComplex (pbcModules Y (pbcAdicCompletion Y dA)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (R := pbcAdicCompletion Y dA) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
          (R := pbcAdicCompletion Y dA) (P.X n)) →
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcDerivedExtend φX).map (pbcActualPullComplexCounit g dA P) ≫
          pbcComplexCounit φX
            (((pbcActualModulePull g dA).mapHomologicalComplex (.up ℤ)).obj P) =
        (pbcActualDerivedPull g dB).map (pbcComplexCounit φY P) ≫
          pbcActualPullComplexCounit g dB
            (((pbcExtend φY).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((pbcActualScalarOrdinaryPullComplexIso g dA dB φY φX hφ).hom.app
            P) := by
  sorry

/-- The canonical derived coefficient/pullback comparison, with its normalization retained.
Source: Stacks Tag 0D6D
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
def pbcActualScalarDerivedPullIso :=
  (pbcActualScalarDerivedPullIso_exists g dA dB φY φX hφ).exists.choose

/-- The direct-image scalar comparison is the actual adjunction mate of the normalized
ordinary-derived pullback comparison, before completeness or constructibility.
Source: Stacks Tag 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
def pbcActualScalarDirectImageMap :
    pbcActualDerivedPush g dA ⋙ pbcDerivedExtend φY ⟶
      pbcDerivedExtend φX ⋙ pbcActualDerivedPush g dB :=
  (mateEquiv (pbcActualDerivedAdjunction g dA) (pbcActualDerivedAdjunction g dB)
    (TwoSquare.mk _ _ _ _ (pbcActualScalarDerivedPullIso g dA dB φY φX hφ).hom)).natTrans

end AlgebraicGeometry.Scheme
