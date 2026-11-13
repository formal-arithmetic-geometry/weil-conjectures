/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Unbounded.ProperUnboundedCoproducts

/-!
# Proper direct image of unbounded complexes: statement

The theorem states the three assertions for both coefficient choices in the current
condensed model.  The two existing predicates expand the degreewise ind-constructible
condition, the two amplitude bounds, the canonical finite truncation window, and the
canonical arbitrary-direct-sum comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Proper direct image of unbounded ind-constructible complexes, with its finite
cohomological window and arbitrary direct sums, for both `E` and `ℚ̄_ℓ` coefficients. -/
theorem properUnboundedWindow_statement
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀]
    (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (_hk : Finite k ∨ IsAlgClosed k)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (d : ℤ)
    (hd : ∀ (y : Y) (n : ℕ),
      (n : WithBot ℕ∞) ≤ topologicalKrullDim
        (pullback p (Spec.map (CommRingCat.ofHom
          (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
            Y.fromSpecResidueField y) : Scheme.{u}) → (n : ℤ) ≤ d) :
    ProperUnboundedWindowAssertions (Profinite.continuousMapRingObj.{u} E) p d ∧
      ProperUnboundedCoproductAssertions (Profinite.continuousMapRingObj.{u} E) p ∧
      ProperUnboundedWindowAssertions (Profinite.padicAlgClRingObj.{u} ℓ) p d ∧
      ProperUnboundedCoproductAssertions (Profinite.padicAlgClRingObj.{u} ℓ) p := by
  sorry

end AlgebraicGeometry.ProEtale
