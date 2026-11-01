/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaPairingData
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionInvertibility

/-! # The prescribed scalar comparisons for the integral dual formula -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefDualFormulaScalarTranspose

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)

/-- The evaluation-defined beta is invertible on the actual constructible domain,
independently of normalized tensor presentation.
Source: lem-coef-integral-finite-extension, beta clause
(blueprint: def-coef-dual-formula-scalar-data).
Proof: the finite-free scalar Hom comparison preserves evaluation on K-flat models.
Its complete version is obtained by the specified completion maps. The dualizing
comparison is the scalar-extended structural-counit transpose. Finite Verdier duality
makes their composite invertible on every finite level; the coherent reduction/limit
realization and derived completeness give invertibility of the displayed beta.
Changing a normalized tensor presentation preserves its evaluation transpose, so the
conclusion holds for both supplied presentations. -/
theorem beta_isIso (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))]
    (wE : IntegralFiniteExtension.DualizingDatum l W D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l W D hl L)
    (a : IntegralHom.TensorPresentation.{u, u} W
      (completedIntegralCommRingSheafUnrestricted l E W))
    (b : IntegralHom.TensorPresentation.{u, u} W
      (completedIntegralCommRingSheafUnrestricted l L W))
    (K : sfIntegralConstructibleCategory l E W) :
    IsIso (IntegralFiniteExtension.beta l E L i W D hl wE wL a b K.obj K.property.1) := by
  obtain ⟨_, hu, hv⟩ :=
    IntegralFiniteExtension.comparison_invertibility l E L i W D hl wE wL a b
  let := hu
  let := hv K wE.omega
  unfold IntegralFiniteExtension.beta
  let : IsIso (Prod.mkHom
      (𝟙 (op ((integralScalarExtensionOfUniverses l E L i W).obj K.obj)))
      (IntegralFiniteExtension.u l E L i W D hl wE wL)) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, hu⟩
  exact IsIso.comp_isIso' (hv K wE.omega) (Functor.map_isIso _ _)

/-- The specified scalar beta, viewed as an isomorphism using its invertibility theorem.
Source: blueprint beta convention
(blueprint: def-coef-dual-formula-scalar-data). -/
def betaIso (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))]
    (wE : IntegralFiniteExtension.DualizingDatum l W D hl E)
    (wL : IntegralFiniteExtension.DualizingDatum l W D hl L)
    (a : IntegralHom.TensorPresentation.{u, u} W
      (completedIntegralCommRingSheafUnrestricted l E W))
    (b : IntegralHom.TensorPresentation.{u, u} W
      (completedIntegralCommRingSheafUnrestricted l L W))
    (K : sfIntegralConstructibleCategory l E W) :=
  @asIso _ _ _ _ (IntegralFiniteExtension.beta l E L i W D hl wE wL a b K.obj K.property.1)
    (beta_isIso D l hl E L i W wE wL a b K)

/-- The finite-free completed compact-support comparison in the ambient realization.
The direction is T_Y F_E to F_L T_X. Both completions and the proper/open scalar mate
are the published canonical maps. Source: blueprint definition of alpha
(blueprint: def-coef-dual-formula-scalar-data). -/
def supportScalar (K : sfIntegralConstructibleCategory l E X) :
    (integralScalarExtension l E L i Y).obj
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj K).obj ⟶
      (PurCompactSupport.image (PurCompactSupport.completed l L) c).obj
        ((integralScalarExtension l E L i X).obj K.obj) :=
  (IntegralFiniteExtension.completion l E L i Y _
    ((sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj K).property.1).inv ≫
  (pbcDerivedExtend (completedCoefficientMap l E L i Y)).map
    ((sfQcqsCompactSupportRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app K) ≫
  (PurCompactSupport.comparison (PurCompactSupport.completedChange l E L i) c).app K.obj ≫
  (PurCompactSupport.image (PurCompactSupport.completed l L) c).map
    (IntegralFiniteExtension.completion l E L i X K.obj K.property.1).hom

/-- The prescribed finite-free comparison is invertible on constructible complexes.
Source: blueprint alpha convention, finite-free completed scalar comparison
(blueprint: def-coef-dual-formula-scalar-data).
Proof: choose an R-basis of S to compute ordinary scalar extension as a finite sum.
Open extension, proper derived image and the Roos total limit distribute over this
finite sum. The universal tensor and quotient normalizations identify that distributive
map with supportScalar, including its two completion conjugations. Hence it is invertible;
the construction is independent of the basis. -/
theorem supportScalar_isIso (K : sfIntegralConstructibleCategory l E X) :
    IsIso (supportScalar D l hl E f c L i K) := by
  let (x : X) : Invertible (l : X.residueField x) :=
    (by
      simpa using (finiteFieldDatumPrimeUnit D l hl).map
        ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
          IsUnit (l : X.residueField x)).invertible
  have hK : finiteTorConstructibleIntegral l E X K.obj := by
    rw [← (integral_residue_tor D l hl E X).2]
    exact K.property
  have hcomp : IsIso ((PurCompactSupport.comparison
      (PurCompactSupport.completedChange l E L i) c).app K.obj) :=
    (PurCompactSupport.integralCoefficientComparison l E L i D hl f c K.obj hK).2.2.2.1
  unfold supportScalar
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' hcomp ?_))
  · exact Iso.isIso_inv _
  · exact ((pbcDerivedExtend (completedCoefficientMap l E L i Y)).mapIso
      ((sfQcqsCompactSupportRealization l E D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c).app K).symm).isIso_hom
  · exact ((PurCompactSupport.image (PurCompactSupport.completed l L) c).mapIso
      (IntegralFiniteExtension.completion l E L i X K.obj K.property.1)).isIso_hom

/-- The canonical finite-free completed support isomorphism, in the ambient realization.
Source: blueprint definition of alpha
(blueprint: def-coef-dual-formula-scalar-data). -/
def supportScalarIso (K : sfIntegralConstructibleCategory l E X) :=
  @asIso _ _ _ _ (supportScalar D l hl E f c L i K)
    (supportScalar_isIso D l hl E f c L i K)

/-- The canonical scalar comparison d_M for the integral dual formula, with precisely
contravariant order: D_X,L(f_L^*(beta_Y inverse) followed by c inverse), then beta_X.
Source: blueprint displayed definition of d_M
(blueprint: def-coef-dual-formula-scalar-data). -/
def dualFormulaScalar
    (wEX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wEY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (wLX : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (wLY : IntegralFiniteExtension.DualizingDatum l Y D hl L)
    (aEX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aEY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (aLX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (aLY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l L Y))
    (M : sfIntegralConstructibleCategory l E Y) :
    (integralScalarExtension l E L i X).obj (formulaObject D l hl E f wEX wEY M) ⟶
      formulaObject D l hl L f wLX wLY
        ((sfConstructibleIntegralScalarExtension D.p l hl E L i Y).obj M) :=
  IntegralFiniteExtension.beta l E L i X D hl wEX wLX
      (normalizedTensorPresentation X _ aEX) (normalizedTensorPresentation X _ aLX)
      (pullDualValue D l hl E f wEY M).obj (pullDualValue D l hl E f wEY M).property.1 ≫
    (IntegralVerdier.dual l L X wLX.omega.obj).map
      ((integralDerivedPullback.{u, u} l L f).map (betaIso D l hl E L i Y wEY wLY
        (normalizedTensorPresentation Y _ aEY) (normalizedTensorPresentation Y _ aLY) M).inv ≫
        (scalarPullbackCompleted l E L i f (dualValue D l hl E Y wEY M).obj
          (dualValue D l hl E Y wEY M).property.1
          (pullDualValue D l hl E f wEY M).property.1).inv).op

end WeilConjectures.CoefDualFormulaScalarTranspose
