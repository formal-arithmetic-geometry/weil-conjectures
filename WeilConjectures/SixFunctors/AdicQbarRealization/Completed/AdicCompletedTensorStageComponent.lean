/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonComponent
public import WeilConjectures.SixFunctors.Common.CommonStageInclusionTensorNaturality

/-! # Naturality of the explicit completed tensor components

Source: BS Remark 6.8.15; HRS Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.AdicQbarRealization.ordinary

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)

/-- The completed tensor component evaluated at a single rational coefficient stage.
Every rational object has its original integral object; the last comparison is the
existing natural inclusion tensorator. Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: def-sf-adic-completed-tensor-stage-component). -/
def completedTensorStageComponent
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : CompletedTensorFiniteModel l X R closed models E)
    (K L : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    closed.tensor.obj
      ((ordinary l X R).obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj K),
       (ordinary l X R).obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj L)) ≅
      (ordinary l X R).obj ((commonStageDerivedTensor l (PadicAlgCl l) X).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj K,
         (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj L)) :=
  completedTensorIntegralComponent l X R closed models E N K.obj L.obj ≪≫
    (Functor.isoWhiskerRight (commonInclusionTensorComparison l (PadicAlgCl l) X E)
      (ordinary l X R)).app (K, L)

end WeilConjectures.AdicQbarRealization
