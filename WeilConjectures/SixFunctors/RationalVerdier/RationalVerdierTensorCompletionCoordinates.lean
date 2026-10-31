/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Representative calculations for tensor completion and scalar extension

Source: the normalized completion and tensor calculations in the blueprint proof of
lem-coef-integral-finite-extension, paragraphs 1 and 4.
(blueprint: lem-coef-rational-verdier-tensor-completion-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier

attribute [local irreducible] HasDerivedCategory.standard
  integralOrdinaryScalar completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted CochainComplex.mappingCone
  CochainComplex.mappingCocone towerTransitionEndomorphism
attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local implicit_reducible] integralOperationsTensorComplexFunctor
  integralOperationsRoos integralOperationsRoosFunctor Functor.mapHomologicalComplex

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))] in
attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
/-- The two normalized coordinates of the recorded tensor completion chain.
Source: blueprint lem-coef-integral-finite-extension.proof.md, paragraph 1;
constructibleTensorCompletion fixes these coordinates before derived localization.
(blueprint: lem-coef-rational-verdier-tensor-completion-coordinates).
Proof: unfold the definition selecting the normalized completion chain. The
selected witness's first clause is precisely the quotient tensor formula, and
its second clause is the zero shifted coordinate. Project these two clauses. -/
theorem tensor_completion_coordinates :
    (∀ (P Q : CochainComplex (integralTowerModules l E X) ℤ)
      (p q : ℤ) (n : ℕ) (U : X.ProEtᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      ((((completionChain D l hl X E).app (P, Q) ≫
        CochainComplex.mappingCocone.fst
          (scalarRoosBoundary ((integralOperationsTensorTowerFunctor l E X).obj (P, Q))) ≫
        Pi.π (fun n ↦ ((integralOperationsTensorTowerFunctor l E X).obj (P, Q)).obj (op n)) n).f
          (p + q)).val.app U) (constructibleTensorTotalSection l E X P Q p q U x y) =
      integralOperationsTotalTensorSection l E X n P Q p q U
        (unrestrictedIntegralTensorSection l E X n (P.X p) U 1 x)
        (unrestrictedIntegralTensorSection l E X n (Q.X q) U 1 y)) ∧
    (∀ (P Q : CochainComplex (integralTowerModules l E X) ℤ) (i j : ℤ)
      (h : i + -1 = j),
      ((completionChain D l hl X E).app (P, Q)).f i ≫
        (CochainComplex.mappingCocone.snd
          (scalarRoosBoundary ((integralOperationsTensorTowerFunctor l E X).obj (P, Q)))).v i j h =
        0) := by
  unfold completionChain
  exact ⟨(third_exists_first (@constructibleTensorCompletion l _ E _ _ _ X
    (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
    (quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of D.k)))
    (units D l hl X))).choose_spec.choose_spec.choose_spec.1,
    (third_exists_first (@constructibleTensorCompletion l _ E _ _ _ X
    (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
    (quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of D.k)))
    (units D l hl X))).choose_spec.choose_spec.choose_spec.2.1⟩

end WeilConjectures.RationalVerdier
