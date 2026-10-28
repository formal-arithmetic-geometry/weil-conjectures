/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Sheaf.SixFunctors.IntegralDualizingSupportSystemHom
import Sheaf.SixFunctors.IntegralDualizingSystemTraceExistence
import Sheaf.SixFunctors.IntegralDualizingSystemFiniteEvaluation

/-! # Finite exceptional adjunction on the quotient sequence site -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The finite exceptional adjunction, before integral compact support is realized.
Its target is quotient-system Hom from quotient-system compact support, so this
comparison contains no derived limit or integral compact-support value.

Source: prop-coef-integral-dualizing, second paragraph, middle displayed comparison
and compatibility of the exceptional counits with reduction.
(blueprint: lem-coef-integral-dualizing-system-finite-adjunction).

Proof: obtain a trace on Q normalized by the fixed finite exceptional counits,
using the compatible identifications eQ and hQ. Define the comparison by the
base-linear projection/evaluation word and its two adjunction transposes.
Dinaturality of that word proves naturality in K before finite evaluation.
For each K, the finite mapping adjunction makes every exact scalar-tower
evaluation of this particular comparison invertible. Exact evaluation commutes
with homology, so it jointly detects invertibility. Componentwise invertibility
then gives the natural isomorphism. The remaining geometric obligations are the
normalized trace construction and finite invertibility, stated separately; this
is a decomposition of the original hole, not a closed geometric proof. -/
theorem integralDualizing_system_finite_adjunction
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n)
    (hQ : ∀ {m n : ℕ} (h : n ≤ m),
      (coefficientSequenceDerivedTransition l E X h).app (coefTraceInput l E X Q) ≫
          (normalizedDVRRes l E X h).map (eQ n).hom =
        (eQ m).hom ≫
          (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
            (integralDualizingFiniteComparison l E D X hl h)) :
    Nonempty ((sfIntegralConstructible l E X).ι.op ⋙ coefPairingHom l E X S Q ≅
      integralDualizingSupportSystemHom D l E X S G) := by
  obtain ⟨t⟩ := integralDualizingSystemTraceData_exists D l hl E X S G Q eQ hQ
  let α := integralDualizingSystemAdjunctionMap D l E X S G Q t.trace
  have (K : (sfIntegralConstructibleCategory l E X)ᵒᵖ) : IsIso (α.app K) :=
    coefPairingDerived_isIso_of_evaluations l E _
      (fun n ↦ integralDualizingSystemAdjunctionMap_evaluation_isIso D l hl E X S G Q eQ t K n)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact ⟨asIso α⟩

end WeilConjectures
