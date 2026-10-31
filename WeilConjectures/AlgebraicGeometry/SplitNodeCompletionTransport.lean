/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import WeilConjectures.RingTheory.AdicCompletionRingEquiv

/-!
# Transport of a split nodal completion

Source: Stacks Project, Curves, Tag 0E38, the cases where the subcurve agrees locally
with the ambient curve (blueprint: lem-trf-split-node-completion-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open IsLocalRing

namespace AlgebraicGeometry

private noncomputable def powerSeriesCoeffEquiv
    {F G : Type u} [Field F] [Field G] (e : F ≃+* G) :
    MvPowerSeries (Fin 2) F ≃+* MvPowerSeries (Fin 2) G where
  __ := MvPowerSeries.map e.toRingHom
  invFun := MvPowerSeries.map e.symm.toRingHom
  left_inv f := by ext n; simp
  right_inv f := by ext n; simp

/-- Isomorphic local rings, with compatible ground-field and residue-field structures,
have the same split nodal completion condition.

Source: Stacks Project, Curves, Tag 0E38, unique-component and all-components cases.
(blueprint: lem-trf-split-node-completion-transport).

Proof: The local-ring equivalence identifies the maximal ideals and hence induces an
equivalence on each quotient by its powers, and on the inverse limits. Map the coefficients
of the two-variable power series ring by the residue-field equivalence. This fixes the two
variables and therefore carries the ideal (uv) to (uv), giving a quotient equivalence.
Compose the inverse completion equivalence, the original nodal equivalence, and this quotient
equivalence. Compatibility with the completion maps and with constants proves the scalar
identity. No Noetherianity or finite-type assumption is needed for this transport. -/
theorem split_node_completion_transport
    {k : Type u} [Field k] {A : Type v} {B : Type w}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    {F G : Type u} [Field F] [Field G]
    (α : k →+* A) (β : k →+* B) (ρ : k →+* F) (σ : k →+* G)
    (eA : A ≃+* B) (eF : F ≃+* G)
    (hA : ∀ a, eA (α a) = β a) (hF : ∀ a, eF (ρ a) = σ a)
    (e : AdicCompletion (maximalIdeal A) A ≃+*
      (MvPowerSeries (Fin 2) F ⧸
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) F) * MvPowerSeries.X 1}))
    (he : ∀ a : k, e (AdicCompletion.of (maximalIdeal A) A (α a)) =
      Ideal.Quotient.mk _ (MvPowerSeries.C (ρ a))) :
    ∃ e' : AdicCompletion (maximalIdeal B) B ≃+*
        (MvPowerSeries (Fin 2) G ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) G) * MvPowerSeries.X 1}),
      ∀ a : k, e' (AdicCompletion.of (maximalIdeal B) B (β a)) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ a)) := by
  classical
  have hm : maximalIdeal B = (maximalIdeal A).map eA.toRingHom := by
    ext b
    rw [Ideal.mem_map_iff_of_surjective eA.toRingHom eA.surjective]
    constructor
    · intro hb
      refine ⟨eA.symm b, ?_, eA.apply_symm_apply b⟩
      change ¬ IsUnit (eA.symm b)
      intro h
      apply hb
      have h' : IsUnit (eA (eA.symm b)) := h.map eA.toMonoidHom
      simpa only [eA.apply_symm_apply] using h'
    · rintro ⟨a, ha, rfl⟩
      change ¬ IsUnit (eA a)
      intro h
      apply ha
      have h' : IsUnit (eA.symm (eA a)) := h.map eA.symm.toMonoidHom
      simpa only [eA.symm_apply_apply] using h'
  obtain ⟨E, hE⟩ := AdicCompletion.exists_ringEquiv (maximalIdeal A) (maximalIdeal B) eA hm
  let p := powerSeriesCoeffEquiv eF
  have hp : Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) G) *
        MvPowerSeries.X 1} =
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) F) *
        MvPowerSeries.X 1}).map p.toRingHom := by
    rw [Ideal.map_span]
    simp [p, powerSeriesCoeffEquiv]
  let q := Ideal.quotientEquiv _ _ p hp
  refine ⟨E.symm.trans (e.trans q), fun a ↦ ?_⟩
  have hEa : E (AdicCompletion.of (maximalIdeal A) A (α a)) =
      AdicCompletion.of (maximalIdeal B) B (β a) := by
    have h := DFunLike.congr_fun hE (α a)
    change E (AdicCompletion.of (maximalIdeal A) A (α a)) =
      AdicCompletion.of (maximalIdeal B) B (eA (α a)) at h
    rwa [hA] at h
  change q (e (E.symm (AdicCompletion.of (maximalIdeal B) B (β a)))) = _
  rw [← hEa, E.symm_apply_apply, he]
  change Ideal.Quotient.mk _ (MvPowerSeries.map eF.toRingHom (MvPowerSeries.C (ρ a))) = _
  rw [MvPowerSeries.map_C]
  exact congrArg (fun c ↦ Ideal.Quotient.mk _ (MvPowerSeries.C c)) (hF a)

end AlgebraicGeometry
