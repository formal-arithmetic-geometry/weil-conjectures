/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaPullCompletion
public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaSignedSymmetry
public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaNaturalEvaluation

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

/-- Projection normalization for the relative integral dualizing trace.
The finite maps are the structural-counit transposes defined above.
Source: blueprint Steps 2 and 11
(blueprint: def-coef-dual-formula-pairing-data). -/
def TraceNormalized
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (t : (sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj wX.omega ⟶ wY.omega) : Prop :=
  ∀ n : ℕ,
    (scalarReductionDerivedExtension l E Y n).map
        ((sfIntegralConstructible l E Y).ι.map t) ≫ (wY.reduction n).hom =
      (sfCompactSupportFiniteReductionIso l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E wX.omega n).hom ≫
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
        (wX.reduction n).hom ≫ finiteTrace D l E f c n

/-- The actual integral dual-formula object, using completed pullback and ordinary
internal Hom into the specified dualizing object. Source: blueprint definition of kappa
(blueprint: def-coef-dual-formula-pairing-data). -/
def formulaObject
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (M : sfIntegralConstructibleCategory l E Y) : IntegralVerdier.Ambient l E X :=
  (IntegralVerdier.dual l E X wX.omega.obj).obj
    (op ((integralDerivedPullback.{u, u} l E f).obj
      ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj))))

/-- The constructible value of the specified integral Verdier dual. The membership
proof is extracted from the recorded integral Verdier theorem.
Source: blueprint integral Verdier convention
(blueprint: def-coef-dual-formula-pairing-data). -/
def dualValue (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))]
    (w : IntegralFiniteExtension.DualizingDatum l W D hl E)
    (K : sfIntegralConstructibleCategory l E W) : sfIntegralConstructibleCategory l E W :=
  ⟨(IntegralVerdier.dual l E W w.omega.obj).obj (op K.obj),
    (Exists.choose (Exists.choose_spec (Exists.choose_spec (Exists.choose_spec
      (Exists.choose_spec (Exists.choose_spec
        (integral_verdier_biduality D l hl E W w.omega w.reduction))))))) K⟩

/-- Completed pullback of the constructible dual, with residue inverses induced from k.
Source: blueprint definition of d_M
(blueprint: def-coef-dual-formula-pairing-data). -/
def pullDualValue (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (M : sfIntegralConstructibleCategory l E Y) : sfIntegralConstructibleCategory l E X :=
  (@constructibleIntegralPullback l _ E _ _ _ X Y f
    (fun x ↦ (by
      simpa using (finiteFieldDatumPrimeUnit D l hl).map
        ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
          IsUnit (l : X.residueField x)).invertible)
    (fun y ↦ (by
      simpa using (finiteFieldDatumPrimeUnit D l hl).map
        ((Y ↘ Spec (.of D.k)).residueFieldAlgebraMap y) :
          IsUnit (l : Y.residueField y)).invertible)).obj
      (dualValue D l hl E Y wY M)

/-- The actual projection, completion, signed evaluation and relative-trace word.
Source: blueprint trace transpose, Steps 2--3
(blueprint: def-coef-dual-formula-pairing-data). -/
def formulaTracePairing
    (wX : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (aX : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l E c.Z))
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (sX : IntegralVerdier.SignedSymmetry X _ aX)
    (t : (sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj wX.omega ⟶ wY.omega)
    (K : sfIntegralConstructibleCategory l E X)
    (M : sfIntegralConstructibleCategory l E Y)
    (h : K.obj ⟶ formulaObject D l hl E f wX wY M) :=
  ((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c
      (IntegralFiniteExtension.tensorModel X aX)
      (IntegralFiniteExtension.tensorModel c.Z aZ)
      (IntegralFiniteExtension.tensorModel Y aY)
      (PurCompactSupport.completedPull_comp l E c.i c.g)).app K.obj).app
        ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)) ≫
    (PurCompactSupport.image (PurCompactSupport.completed l E) c).map
      (aX.tensor.map (Prod.mkHom (𝟙 K.obj)
        ((pullCompletion l E f).app
          ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)))) ≫
      ((normalizedSignedSymmetry X _ aX sX).swap K.obj ((integralDerivedPullback.{u, u} l E f).obj
        ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)))).hom ≫
      aX.tensor.map (Prod.mkHom (𝟙 _) h) ≫
      (canonicalEvaluationAdjunction X _ aX ((integralDerivedPullback.{u, u} l E f).obj
        ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)))).counit.app wX.omega.obj) ≫
    (sfQcqsCompactSupportRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c).hom.app wX.omega ≫
    (sfIntegralConstructible l E Y).ι.map t

/-- Evaluation of an arbitrary ambient morphism into the constructible target.
Source: blueprint tensor-Hom evaluation in Steps 2--3
(blueprint: def-coef-dual-formula-pairing-data). -/
def formulaEvaluationPairing
    (wY : IntegralFiniteExtension.DualizingDatum l Y D hl E)
    (aY : IntegralHom.TensorPresentation.{u, u} Y
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (P : IntegralVerdier.Ambient l E Y)
    (M : sfIntegralConstructibleCategory l E Y) (g : P ⟶ M.obj) :=
  aY.tensor.map (Prod.mkHom g
      (𝟙 ((IntegralVerdier.dual l E Y wY.omega.obj).obj (op M.obj)))) ≫
    (canonicalEvaluationAdjunction Y _ aY M.obj).counit.app wY.omega.obj

end WeilConjectures.CoefDualFormulaScalarTranspose
