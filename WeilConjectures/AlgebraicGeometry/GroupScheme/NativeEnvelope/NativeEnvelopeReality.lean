/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeNormalizedRealEnvelope
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import Mathlib.LinearAlgebra.Trace
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeNormalizedTwistPureZero
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeEnvelopeLocalModel
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeEnvelopeLisse
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeLisseLocalFrobeniusModule

/-! # Reality of the normalized condensed envelope

Source: latest blueprint, sk-prop-wrp-real-envelope/lem-wf-envelope-real.md
and its proof (blueprint: lem-wf-envelope-real).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.NativeEnvelope

private theorem isAlgClosed_ulift_padic (l : ℕ) [Fact l.Prime] :
    IsAlgClosed (ULift.{u + 1} (PadicAlgCl l)) := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  let e : ULift.{u + 1} (PadicAlgCl l) ≃+* PadicAlgCl l := ULift.ringEquiv
  let q := p.map e.toRingHom
  have hdeg : q.degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact (Polynomial.degree_pos_of_irreducible hp).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hdeg
  refine ⟨ULift.up x, ?_⟩
  have hxe : e (Polynomial.eval (ULift.up x) p) = 0 := by
    calc
      e (Polynomial.eval (ULift.up x) p) =
          Polynomial.eval₂ e.toRingHom (e (ULift.up x)) p :=
        (Polynomial.eval₂_at_apply e.toRingHom (ULift.up x)).symm
      _ = Polynomial.eval x q := by
        have he : e (ULift.up x) = x := rfl
        rw [he, Polynomial.eval_map]
      _ = 0 := hx
  simpa [e] using hxe

/-- The normalized envelope of a lisse pure Weil sheaf is real and lisse.
Source: latest blueprint, lem-wf-envelope-real, entire statement
(blueprint: lem-wf-envelope-real).
Proof: the constant twist changes every local weight by -w, hence has weight zero.
The recorded tensor and dual fibre comparisons identify dual Frobenius with inverse
transpose. Thus if beta occurs in the twisted fibre, its image under iota has norm one,
and iota(beta inverse) is its complex conjugate. The two root multisets, with their
algebraic multiplicities, form a conjugation-stable union. The polynomial reality
criterion gives Real. Finite-free local trivializations show that the twist, its
internal dual and their finite direct sum are lisse, also on disconnected schemes
and on zero-rank components. -/
theorem realEnvelope_real_lisse
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom]
    (F : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    (hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) F.carrier)
    (hpure : NativeL2.Pure D l X₀ F iota w) (b : (PadicAlgCl l)ˣ)
    (hb : ‖iota b‖ = (D.q : ℝ) ^ (-w / 2)) :
    NativeCondensedWeil.Real D l X₀ (realEnvelope D l X₀ hl F b) iota ∧
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj l)
        (realEnvelope D l X₀ hl F b).carrier := by
  refine ⟨?_, normalizedEnvelope_lisse D l hl X₀ F hF b⟩
  have hzero := normalizedTwist_pure_zero D l hl X₀ F iota w hpure b hb
  have hraw : IsLocallyFree
      (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber X₀).left)
      F.carrier := (isLocallyFree_iff F.carrier).mpr hF
  have hraw₀ : IsLocallyFree
      (condensedRingObj (Profinite.padicAlgClRingObj l) (D.geometricFiber X₀).left)
      (normalizedTwist D l X₀ hl F b).carrier := by
    change IsLocallyFree _ (F.carrier ⊗ (𝟙_ _))
    exact hraw.of_iso (ρ_ F.carrier).symm
  have hF₀ := (isLocallyFree_iff (normalizedTwist D l X₀ hl F b).carrier).mp hraw₀
  intro x i hi n e j
  let M := localFrobeniusModule D l X₀ (normalizedTwist D l X₀ hl F b) hF₀ x i hi
  have hpoly := envelope_local_model D l hl X₀ F b hF₀ x i hi n e
  let ι : ULift.{u + 1} (PadicAlgCl l) →+* ℂ :=
    iota.comp ULift.ringEquiv.toRingHom
  letI : IsAlgClosed (ULift.{u + 1} (PadicAlgCl l)) :=
    isAlgClosed_ulift_padic l
  have hM : M.IsPureOfWeight ι 1 0 := by
    intro α hα
    have hα₀ := localTransport_hasEigenvalue_closedOperator D l X₀
      (normalizedTwist D l X₀ hl F b) x i hi
      (localFrobeniusModule_hasEigenvalue_transport D l X₀
        (normalizedTwist D l X₀ hl F b) hF₀ x i hi hα)
    dsimp [ι]
    change ‖iota (ULift.ringEquiv α)‖ = ((1 : ℕ) : ℝ) ^ ((0 : ℝ) / 2)
    simpa [ULift.ringEquiv] using hzero x i hi α hα₀
  have hreal := hM.isReal_prod_dual (by decide : 0 < (1 : ℕ)) j
  apply Complex.conj_eq_iff_im.mp
  rw [hpoly]
  exact hreal

end WeilConjectures.NativeEnvelope
