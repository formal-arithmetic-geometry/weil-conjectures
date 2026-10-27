/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R9
-/
module

public import Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData
public import Sheaf.Paper.EtaleSystemCofinalData

/-! # Uniform bounds for ramified left recovery

Source: Zheng, Construction 4.1 and Proposition 5.24; integral scalar mates, step 2
(blueprint: lem-sf-ramified-system-recovery-bounds).
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  Opposite SheafOfModules
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

/-- Selected left recovery preserves finite constructibility and the original common
cohomological and Tor intervals. Normalization is the only condition on transitions.

Source: Zheng, Construction 4.1 and Proposition 5.24; integral scalar mates, step 2
(blueprint: lem-sf-ramified-system-recovery-bounds).

Proof: at level m selectedDerivedBelow identifies recovery with derived extension
of N at t(m) along A_{L,r(t(m))+1} → A_{L,m+1}. Change of rings and balanced
associativity show that tensoring this object with any degree-zero target module
is the same test of N at t(m) with that module restricted to the source ring.
Thus its Tor interval stays [c,d]. Finite constructibility is preserved by this
finite quotient extension, using a flat-term K-flat model on each constructible
stratum. For the cohomological interval, the source and target are quotients of
the same DVR by positive powers. A perfect stalk complex over the larger quotient
can be represented minimally by a bounded finite free complex. Its extreme
nonzero degrees are detected after reduction to the residue field, hence already
by its cohomology over any positive quotient. Consequently derived extension to
the smaller quotient preserves the original interval [a,b]. This applies on each
constructible stratum and therefore to the sheaf complex. Transfer all assertions
through the selected evaluation comparison, for every m. -/
theorem ramifiedSystemRecoveryBounds
    (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (e : ℕ+) (_he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
    (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    (S : SystemLevelLeftExtensionTheory.{u + 1, u, u + 1}
      (C := T.ProEt) (J := Scheme.ProEt.topology T)) :
    let B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
      coefficientSequenceCommRingSystem.{u, u} l L.carrier T
    let r := Etale.SystemProjection.cofinalRamification e
      (Nat.one_le_iff_ne_zero.mpr e.ne_zero)
    ∀ (N : DerivedCategory (StrictRingSystem.{u + 1, u, u + 1}
        (selectedSystemRings.{u + 1, u, u + 1} B r))) (a b c d : ℤ),
      (∀ {m n : ℕ} (h : m ≤ n),
        IsIso (((systemDerivedTensorAdj.{u + 1, u, u + 1} S.scalar
          (selectedSystemRings.{u + 1, u, u + 1} B r) h).homEquiv _ _).symm
          ((SystemLevelLeftExtensionTheory.transition.{u + 1, u, u + 1} S
            (selectedSystemRings.{u + 1, u, u + 1} B r) h).app N))) →
      (∀ n : ℕ,
        finiteTorConstructible l L.carrier (r n + 1) (Nat.succ_pos _) T
          ((derivedSystemEvaluation.{u + 1, u, u + 1}
            (selectedSystemRings.{u + 1, u, u + 1} B r) n).obj N) ∧
        ((derivedSystemEvaluation.{u + 1, u, u + 1}
            (selectedSystemRings.{u + 1, u, u + 1} B r) n).obj N).IsGE a ∧
        ((derivedSystemEvaluation.{u + 1, u, u + 1}
            (selectedSystemRings.{u + 1, u, u + 1} B r) n).obj N).IsLE b ∧
        HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l L.carrier (r n + 1))
          ((derivedSystemEvaluation.{u + 1, u, u + 1}
            (selectedSystemRings.{u + 1, u, u + 1} B r) n).obj N) c d) →
      ∀ m : ℕ,
        finiteTorConstructible l L.carrier (m + 1) (Nat.succ_pos _) T
          ((derivedSystemEvaluation.{u + 1, u, u + 1} B m).obj
            ((S.selected B r).derived.obj N)) ∧
        ((derivedSystemEvaluation.{u + 1, u, u + 1} B m).obj
            ((S.selected B r).derived.obj N)).IsGE a ∧
        ((derivedSystemEvaluation.{u + 1, u, u + 1} B m).obj
            ((S.selected B r).derived.obj N)).IsLE b ∧
        HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l L.carrier (m + 1))
          ((derivedSystemEvaluation.{u + 1, u, u + 1} B m).obj
            ((S.selected B r).derived.obj N)) c d := by sorry

end WeilConjectures.ExceptionalIntegralScalar
