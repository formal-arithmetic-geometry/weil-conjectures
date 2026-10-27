/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.Paper.AdicFiniteRealizationData
import Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
import Sheaf.Paper.CondensedQbarLfpLocalTriviality

/-! # Constructibility in finite adic module presentations

Source: BS Definitions 6.8.1 and 6.8.8; HRS Theorem 7.7 and Lemma 7.9.
(blueprint: lem-sf-adic-finite-constructibility-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace WeilConjectures.AdicFiniteRealization
variable (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ x : T, IsUnit (l : T.presheaf.stalk x))]

/-- Actual finite coefficient legs and the four constructibility comparisons.
Source: finite realization node, step 3; BS Definition 6.8.8; HRS 7.7 and 7.9
(blueprint: lem-sf-adic-finite-constructibility-comparison).

Proof:
1. The point-adjunction comparison identifies the section ring of the pulled-back
continuous E-ring with continuous E-valued functions. Compose with the spectral
coefficient equivalence Shrink.algEquiv to get finiteIso. Its formula on every
section and point gives finite_normalization. Define leg by finiteIso inverse
followed by sectionRingMap of the actual finite-subfield inclusion into Omega.
2. chartComparison naturality for field inclusions and the normalized coefficient
formula in B.coefficient give coefficient_normalization. SectionRingMap preserves
composition, so the two finite inclusions into Omega coincide. Cancel finiteIso
to obtain cocone; leg_normalization holds by its construction.
3. On each finite locally closed stratum, continuous finite-field lfp modules are
locally finite free by condensedField local triviality. The finite-subextension
Omega version is condensedQbar_lfp_locally_free. Conversely a finite free module
has the presentation with zero relations. Pullback to strata respects these
coefficient rings. Apply this in every cohomological degree to identify the internal
constructibility predicates. The bounded standard t-structure gives an ordered
interval by replacing the lower bound with the minimum of both bounds.
4. The section-module equivalence preserves underlying sheaves, finite free objects,
exact sequences and restrictions, hence the local finite free predicates. Its exact
derived equivalence preserves homology and both degree bounds. The exact equivalence
of extension along finiteIso preserves those same data. Transporting the preceding
internal criteria gives finite_sections and closure_sections. Covers allow rank zero
and the empty scheme; the Omega ring remains finite-subextension-valued throughout. -/
theorem adic_finite_constructibility_comparison (C : Core l T) (B : ScalarData l T C) :
    ∃ R : ClosureData l T C B,
      (∀ (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) K,
    AlgebraicGeometry.ProEtale.boundedConstructible
        (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E) K ↔
      internalFiniteFreeTarget T
        (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E) K) ∧
      (∀ K,
    AlgebraicGeometry.ProEtale.boundedConstructible
        (AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) T) K ↔
      internalFiniteFreeTarget T
        (AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) T) K) ∧
      (∀ (E : Padic.FiniteCoefficientFields l (PadicAlgCl l)) K,
    AlgebraicGeometry.ProEtale.boundedConstructible
        (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E) K ↔
      finiteFreeTarget T (rationalCoefficientSheaf l T
        (pbcFiniteField.{u} l (PadicAlgCl l) E))
        ((pbcDerivedExtend (R.finiteIso E).hom).obj
          ((sectionDerived T (AlgebraicGeometry.ProEtale.padicSubfieldRingObj T l E)).obj K))) ∧
      (∀ K,
    AlgebraicGeometry.ProEtale.boundedConstructible
        (AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) T) K ↔
      finiteFreeTarget T (closureRing l T)
        ((sectionDerived T
          (AlgebraicGeometry.ProEtale.condensedRingObj (Profinite.padicAlgClRingObj l) T)).obj K))
      := by sorry

end WeilConjectures.AdicFiniteRealization
