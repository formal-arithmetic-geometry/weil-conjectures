/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorFiniteModels

/-! # Explicit completed tensor comparison at a common finite field

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

/-- On integral representatives, compose scalar tensor, completion, and the fixed
ordinary realization identifications. Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: def-sf-adic-completed-tensor-common-components). -/
@[irreducible] def completedTensorIntegralComponent
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : CompletedTensorFiniteModel l X R closed models E)
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    closed.tensor.obj
      ((ordinary l X R).obj ((tensorStage l X E).obj K),
       (ordinary l X R).obj ((tensorStage l X E).obj L)) ≅
    (ordinary l X R).obj
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj
        ((rationalDerivedTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
          ((sfRationalConstructibleLocalization l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj K,
           (sfRationalConstructibleLocalization l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj L))) :=
  closed.tensor.mapIso (Iso.prod ((R.integral E).app K) ((R.integral E).app L)) ≪≫
    (N.ordinary.app (K.obj, L.obj)).symm ≪≫
    (pbcDerivedExtend (coefficientMap l X R E)).mapIso
      (tensorQuotientIso l X E N.completion K L) ≪≫
    ((R.integral E).app ((constructibleIntegralTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
      (K, L))).symm ≪≫
    (ordinary l X R).mapIso
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).mapIso
        (tensorIntegralObjectIso l X E K L).symm)

attribute [local irreducible] ordinary rationalDerivedTensor commonStageDerivedTensor stageTensor

/-- At a shared coefficient field use the finite comparison directly. Otherwise
transport to the coefficient compositum using the actual isoToStage maps. Every
factor is an explicitly specified isomorphism; the shared-field branch avoids
introducing and then cancelling identity coefficient-extension comparisons.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: def-sf-adic-completed-tensor-common-components). -/
@[irreducible] def completedTensorCommonComponent
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (P Q : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X) :
    closed.tensor.obj ((ordinary l X R).obj P, (ordinary l X R).obj Q) ≅
      (ordinary l X R).obj ((commonStageDerivedTensor l (PadicAlgCl l) X).obj (P, Q)) := by
  classical
  by_cases h : P.stage = Q.stage
  · rcases P with ⟨E, P⟩
    rcases Q with ⟨F, Q⟩
    dsimp only at h
    subst F
    exact completedTensorIntegralComponent l X R closed models E (N E) P.obj Q.obj ≪≫
      (ordinary l X R).mapIso (stageTensor l X (PadicAlgCl l) E P Q)
  · let E := Padic.finiteCoefficientCompositum l (PadicAlgCl l) P.stage Q.stage
    let hP := ((Padic.finiteCoefficientFields_properties l (PadicAlgCl l)).1 P.stage Q.stage).1
    let hQ := ((Padic.finiteCoefficientFields_properties l (PadicAlgCl l)).1 P.stage Q.stage).2
    let a := (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).isoToStage
      P hP
    let b := (GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).isoToStage
      Q hQ
    refine closed.tensor.mapIso
        (Iso.prod ((ordinary l X R).mapIso a) ((ordinary l X R).mapIso b)) ≪≫ ?_
    refine completedTensorIntegralComponent l X R closed models E (N E)
        (P.toStage hP).obj (Q.toStage hQ).obj ≪≫ ?_
    refine (ordinary l X R).mapIso
      (stageTensor l X (PadicAlgCl l) E (P.toStage hP) (Q.toStage hQ)) ≪≫ ?_
    exact (ordinary l X R).mapIso
      ((commonStageDerivedTensor l (PadicAlgCl l) X).mapIso (Iso.prod a.symm b.symm))

end WeilConjectures.AdicQbarRealization
