/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.LisseLocalizationData

/-! # Local freeness after exact scalar localization

Source: Bhatt--Scholze 6.8.2, 6.8.3 and 6.8.14(2); Stacks 07A4 and 0941.
(blueprint: lem-tw-lisse-localization-local-freeness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
open SheafOfModules WeilConjectures.LisseLocalizationInterfaces
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
namespace WeilConjectures.LisseLocalization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The degree-zero module of a lisse object is finite locally free, and the recorded
completed coefficient unit realizes the ordinary rational coefficient unit.
Source: Bhatt--Scholze 6.8.2, 6.8.3 and 6.8.14(2); Stacks 07A4 and 0941
(blueprint: lem-tw-lisse-localization-local-freeness).

Proof: on each defining lisse chart, the completed integral pullback is the derived
limit of finite-coefficient pullbacks of reductions. The pro-etale object inverse-image
comparison identifies those pullbacks with slice restriction. Derived tensor pullback
identifies their reduction tower, naturally in all transitions, with that of the
restricted integral complex. Derived completeness, the normalized slice-limit
comparison and uniqueness of derived limits identify completed pullback with ordinary
slice restriction. Apply rational realization and the scalar-extension comparison to
the defining chartwise rational isomorphisms. A free integral module of rank r maps
to a free rational module of rank r: multiplication sends a tensor (b_i) to (ab_i),
with inverse (a_i) ↦ sum_i a_i tensor e_i. These maps respect sheafification and are
inverse on pure tensors. Exact restriction commutes with H^0, so the resulting
isomorphisms trivialize H^0 of the realization on the same covering sieve. The empty
basis handles rank zero, and ranks can vary from chart to chart. For the unit,
normalized derived completeness identifies the recorded completed coefficient unit
with B[0]; the same multiplication calculation in rank one and exact derived
factorization identify its realization with A[0]. -/
theorem localization_localFreeness (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (dx : LocalizationData l E X)
    (du : ∀ U : X.ProEt, LocalizationData l E U.left)
    (hs : ∀ U : X.ProEt, ∃ c : SliceCoefficients l E U,
      Nonempty (SliceLocalization l E dx U (du U) c) ∧
      SliceLimitCompatibility U (X.adicLisseForget.obj (integralRing l E X)) ∧
      SliceTensorCompatibility (integralRing l E X) U ∧
      SliceTensorCompatibility (rationalRing l E X) U) :
    (∀ K : sfRationalConstructibleCategory l E X,
      rationalLisseHeartProperty l E X K →
        SheafOfModules.IsFiniteLocallyFree
          ((DerivedCategory.homologyFunctor (Modules X (rationalRing l E X)) 0).obj
            (dx.realization.obj K))) ∧
    Nonempty (dx.realization.obj (pullbackTensorRationalUnit l E X) ≅
      (DerivedCategory.singleFunctor (Modules X (rationalRing l E X)) 0).obj
        (SheafOfModules.unit (X.adicLisseForget.obj (rationalRing l E X)))) := by
  sorry

end WeilConjectures.LisseLocalization
