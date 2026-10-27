/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.Paper.PointWeilHeartFlagData
import Sheaf.Paper.PointWeilAlgebraicFlag
import Sheaf.Paper.PointScalarPunctualSpectrum
import Mathlib.Tactic.FieldSimp

/-! # Pure full flags and mixedness in the point Weil heart

Source: latest blueprint, `thm-zl-real-mixed-by-curves`, paragraph 7
(blueprint: lem-zl-point-weil-heart-flag).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (y : {y : (zlPointBase D).left // y ∈ closedPoints (zlPointBase D).left})
  (ι : (zlPointBase D).left.residueField y.val →+* D.k)
  (hι : ι.comp ((zlPointBase D).hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)

private theorem pointPureOfIso (iota : Ω ≃+* ℂ) (w : ℝ)
    {A B : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω} (e : A ≅ B)
    (h : SfIsPunctuallyPureOfWeight D l hl Ω (zlPointBase D) iota.toRingHom A w) :
    SfIsPunctuallyPureOfWeight D l hl Ω (zlPointBase D) iota.toRingHom B w := by
  intro z α hα
  obtain ⟨L, K, ⟨a⟩, rest⟩ := hα
  exact h z α ⟨L, K, ⟨(ObjectProperty.ι _).mapIso e ≪≫ a⟩, rest⟩

private theorem pointScalarPure (iota : Ω ≃+* ℂ)
    (F : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω) (α : Ωˣ)
    (hα : ∀ v : (zlPointWeilFiber D l hl Ω y ι hι).obj F,
      (zlPointWeilFrobenius D l hl Ω y ι hι F).hom v = (α : Ω) • v) :
    SfIsPunctuallyPureOfWeight D l hl Ω (zlPointBase D) iota.toRingHom F
      (2 * Real.log ‖iota (α : Ω)‖ / Real.log (D.q : ℝ)) := by
  intro z β hβ
  obtain ⟨rfl, hz⟩ := zl_point_scalar_punctual_spectrum D l hl Ω y ι hι F α hα z β hβ
  rw [hz]
  have hq : 1 < (D.q : ℝ) := by
    have hn : 1 < D.q := by
      rw [D.cardinality_eq]
      exact Nat.one_lt_pow (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one D.exponent_pos))
        D.prime.one_lt
    exact_mod_cast hn
  have hlog : Real.log (D.q : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hq)
  have ha : iota (α : Ω) ≠ 0 := by
    intro h
    exact α.ne_zero (iota.injective (h.trans (map_zero iota).symm))
  have hr : 0 < ‖iota (α : Ω)‖ := norm_pos_iff.mpr ha
  rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hq)]
  have he : Real.log (D.q : ℝ) *
      (2 * Real.log ‖iota (α : Ω)‖ / Real.log (D.q : ℝ) / 2) =
        Real.log ‖iota (α : Ω)‖ := by
    field_simp [hlog]
  rw [he, Real.exp_log hr]
  rfl

/-- Every raw constructible Weil sheaf at a finite-field point admits a full Frobenius
flag, with one-dimensional pure quotients and a single finite coefficient-heart model.
The datum D is arbitrary, so this includes every finite extension of the base, with
its own cardinality. No reality, semisimplicity or diagonalizability is assumed.

Source: main-20261015, thm-zl-real-mixed-by-curves.proof.md, paragraph 7
(blueprint: lem-zl-point-weil-heart-flag).

Proof: (1) zl_point_weil_algebraic_flag gives the flag H with every algebraic clause,
its finite coefficient model T, Weil monos H.step and isomorphisms from their
Weil-heart cokernels to the quotients H.Q.
(2) On each quotient Frobenius acts by the unit alpha_j. By
zl_point_scalar_punctual_spectrum every punctual eigenvalue equals alpha_j and the
residue field of the sole closed point has cardinality q. With
w_j = 2 log|iota(alpha_j)|/log q, q > 1 and |iota(alpha_j)| > 0 give
q^(w_j/2) = exp(log|iota(alpha_j)|) = |iota(alpha_j)|, so each quotient is pure.
(3) The finitely many weights w_j have an upper bound w (any w when d = 0). H.G and
H.step, with the zero initial object, terminal isomorphism and Weil monos, form the
mixed filtration; purity passes to each cokernel along the isomorphism to H.Q j,
since a finite presentation of one is composed with the isomorphism. The datum D is
arbitrary, so finite base extensions are included. -/
theorem zl_point_weil_heart_flag (iota : Ω ≃+* ℂ)
    (F : sfCommonStageWeilSheaf D l hl (zlPointBase D) Ω) :
    ∃ H : ZlPointWeilFlagDiagram D l hl Ω F,
      ZlPointWeilHeartFlag D l hl Ω y ι hι iota F H ∧
      ∃ T : ZlPointWeilFlagFiniteDiagram D l hl Ω F H,
        ZlPointWeilHeartFlagModel D l hl Ω y ι hι F H T ∧
        ∃ w : ℝ, SfIsMixedOfWeightsAtMost D l hl Ω (zlPointBase D) iota.toRingHom F w := by
  classical
  obtain ⟨H, T, hH, hT, hm, hc⟩ := zl_point_weil_algebraic_flag D l hl Ω y ι hι F
  rcases hH with ⟨hd, hfd, hmono, hstep, hzero, hlast, hrank, hexact,
    hqrank, hscalar, hmonotone, hinvariant, hbij, hgBij, hqBij⟩
  have hp : ∀ j : Fin H.d,
      SfIsPunctuallyPureOfWeight D l hl Ω (zlPointBase D) iota.toRingHom (H.Q j)
        (2 * Real.log ‖iota (H.α j : Ω)‖ / Real.log (D.q : ℝ)) :=
    fun j ↦ pointScalarPure D l hl Ω y ι hι iota (H.Q j) (H.α j) (hscalar j)
  refine ⟨H, ⟨hd, hfd, hmono, hstep, hzero, hlast, hrank, hexact, hqrank,
    hscalar, hp, hmonotone, hinvariant, hbij, hgBij, hqBij⟩, T, hT, ?_⟩
  let weights : Fin H.d → ℝ := fun j ↦
    2 * Real.log ‖iota (H.α j : Ω)‖ / Real.log (D.q : ℝ)
  obtain ⟨w, hw⟩ := (Set.finite_range weights).bddAbove
  refine ⟨w, H.d, H.G, H.step, hzero, ?_, hm, ?_⟩
  · let := hlast
    exact ⟨asIso (H.into (Fin.last H.d))⟩
  · intro j
    obtain ⟨e⟩ := hc j
    exact ⟨weights j, hw (Set.mem_range_self j),
      pointPureOfIso D l hl Ω iota (weights j) e.symm (hp j)⟩

end WeilConjectures
