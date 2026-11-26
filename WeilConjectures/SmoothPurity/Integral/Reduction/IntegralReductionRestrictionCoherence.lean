/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTransitions
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRCompletedRestrictionCoherence

/-! # Coherence of restriction from finite to completed coefficients -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
attribute [local instance] normalizedDVREffectivityLocal1 normalizedDVREffectivityLocal2
  normalizedDVREffectivityLocal3

private theorem inverse_comparison
    {C : Type*} [Category C] {A B T V : C}
    (a : A ≅ B) (b : A ≅ T) (c : T ≅ V) (d : B ≅ V)
    (h : a.inv ≫ b.hom ≫ c.hom = d.hom) :
    c.inv ≫ b.inv ≫ a.hom = d.inv := by
  apply (cancel_mono d.hom).1
  rw [Iso.inv_hom_id, ← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id]

/-- The canonical completed restriction comparisons respect identity and composition. -/
theorem integralReductionRestriction_coherence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) :
    (∀ (n : ℕ) (P : normalizedDVRDerived l E W n),
      (normalizedDVRResCompletedComp.{u, u, u} l E W D hl (Nat.le_refl n)).inv.app P ≫
        (normalizedDVRResCompleted.{u, u, u} l E W D hl n).map
          ((normalizedDVRResUnit.{u, u} l E W n).hom.app P) = 𝟙 _) ∧
    (∀ {c b a : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
        (P : normalizedDVRDerived l E W a),
      (normalizedDVRResCompletedComp.{u, u, u} l E W D hl hab).inv.app P ≫
        (normalizedDVRResCompletedComp.{u, u, u} l E W D hl hbc).inv.app
          ((normalizedDVRRes.{u, u} l E W hab).obj P) ≫
        (normalizedDVRResCompleted.{u, u, u} l E W D hl c).map
          ((normalizedDVRResComp.{u, u} l E W hbc hab).hom.app P) =
      (normalizedDVRResCompletedComp.{u, u, u} l E W D hl (hab.trans hbc)).inv.app P) := by
  have hc := normalizedDVR_completedRestriction_coherence l E W D hl
  constructor
  · intro n P
    rw [← hc.1 n P]
    exact Iso.inv_hom_id_app _ _
  · intro c b a hab hbc P
    exact inverse_comparison
      ((normalizedDVRResCompleted l E W D hl c).mapIso
        ((normalizedDVRResComp l E W hbc hab).app P))
      ((normalizedDVRResCompletedComp l E W D hl hbc).app
        ((normalizedDVRRes l E W hab).obj P))
      ((normalizedDVRResCompletedComp l E W D hl hab).app P)
      ((normalizedDVRResCompletedComp l E W D hl (hab.trans hbc)).app P)
      (hc.2 hbc hab P)

end WeilConjectures
