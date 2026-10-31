/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaScalarData

/-! # Integral trace and formula pairing data -/

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

/-- Scalar transport of the actual uncurried projection--trace pairing.
Source: blueprint lem-coef-rational-operations, proof paragraph 8, Steps 3--4 and 6
(blueprint: lem-coef-dual-formula-pairing-scalar).
Proof: at a positive coefficient quotient insert the evaluation equation defining
beta and the completed-pullback associator into the trace word. Scalar tensor
reassociation commutes with the proper/open projection map by mate pasting.
The absolute structural counit's defining scalar square identifies the two
relative traces. On a finite free coefficient basis these are distributivity
identities, and the equations are basis independent. They identify the extended
trace evaluation with evaluation of the support comparison inverse followed by
the extended morphism. Perform these operations on simultaneous coefficient-system
resolutions with their quotient cocycles. Descend this single mapping-system
identity through reduction and total limit. The finite-free completed comparison
then identifies its support arrow with the specified supportScalarIso. -/
theorem formulaPairing_scalar
    (wEX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wEY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (wLX : IntegralFiniteExtension.DualizingDatum l X D hl L)
    (wLY : IntegralFiniteExtension.DualizingDatum l Y D hl L)
    (aEX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aEZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l E c.Z))
    (aEY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (aLX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (aLZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l L c.Z))
    (aLY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l L Y))
    (sEX : IntegralVerdier.SignedSymmetry X _ aEX)
    (sLX : IntegralVerdier.SignedSymmetry X _ aLX)
    (tE : (sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj wEX.omega ⟶ wEY.omega)
    (tL : (sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c L).obj wLX.omega ⟶ wLY.omega)
    (htE : TraceNormalized D l hl E f c wEX wEY tE)
    (htL : TraceNormalized D l hl L f c wLX wLY tL)
    (K : sfIntegralConstructibleCategory l E X)
    (M : sfIntegralConstructibleCategory l E Y)
    (h : K.obj ⟶ formulaObject D l hl E f wEX wEY M)
    (g : ((sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj K).obj ⟶ M.obj)
    (hp : formulaTracePairing D l hl E f c wEX wEY aEX aEZ aEY sEX tE K M h =
      formulaEvaluationPairing D l hl E wEY aEY _ M
        ((sfQcqsCompactSupportRealization l E D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app K ≫ g)) :
    formulaTracePairing D l hl L f c wLX wLY aLX aLZ aLY sLX tL
      ((sfConstructibleIntegralScalarExtension D.p l hl E L i X).obj K)
      ((sfConstructibleIntegralScalarExtension D.p l hl E L i Y).obj M)
      ((integralScalarExtension l E L i X).map h ≫
        dualFormulaScalar D l hl E f L i wEX wEY wLX wLY aEX aEY aLX aLY M) =
    formulaEvaluationPairing D l hl L wLY aLY _
      ((sfConstructibleIntegralScalarExtension D.p l hl E L i Y).obj M)
      ((supportScalarIso D l hl E f c L i K).inv ≫
        (integralScalarExtension l E L i Y).map g) := by
  -- BLUEPRINT QUESTION: this statement requires the withdrawn coefficient model.
  -- See report.md for the current blueprint comparison; no proof is claimed.
  sorry

end WeilConjectures.CoefDualFormulaScalarTranspose
