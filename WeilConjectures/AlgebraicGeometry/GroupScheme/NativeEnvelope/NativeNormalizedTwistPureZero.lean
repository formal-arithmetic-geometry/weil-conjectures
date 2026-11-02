/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeNormalizedRealEnvelope
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeNormalizedTwistSpectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField

/-! # Weight zero after the native normalizing twist

Source: latest blueprint, the normalization step of lem-wf-envelope-real.
(blueprint: lem-wf-envelope-real-native-pure-zero)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeEnvelope

/-- Normalization by the constant Weil line changes punctual weight w to zero.
Source: latest blueprint, lem-wf-envelope-real.proof.md, normalization paragraph;
lem-wf-constant-twist-weight with weight shift -w.
(blueprint: lem-wf-envelope-real-native-pure-zero).

Proof: at a closed point x of degree d, trivialize the underlying constant line by its
unit section and identify the tensor fibre using the right unitor. Its Frobenius is
b^d times the original Frobenius: the pullback compositors and the point-return maps
respect the unit and its constant scalars, while each of the d Weil transitions
contributes one factor b. This proves conjugacy to b^d A, independently of the chosen
trivialization. Since b is nonzero, its eigenvalues are exactly b^d alpha, where alpha
runs through the eigenvalues of A. Purity gives |iota(alpha)| = q_x^(w/2).
The residue-degree formula q_x = q^d and the normalization |iota(b)| = q^(-w/2)
give |iota(b^d alpha)| = q^(-dw/2) q^(dw/2) = 1 = q_x^(0/2).
The argument applies to every compatible lift. A zero fibre has no eigenvalues. -/
theorem normalizedTwist_pure_zero
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom]
    (F : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    (hpure : NativeL2.Pure D l X₀ F iota w) (b : (PadicAlgCl l)ˣ)
    (hb : ‖iota b‖ = (D.q : ℝ) ^ (-w / 2)) :
    NativeL2.Pure D l X₀ (normalizedTwist D l X₀ hl F b) iota 0 := by
  intro x i hi α hα
  obtain ⟨β, hβ, hαβ⟩ := normalizedTwist_eigenvalues D l hl X₀ F b x i hi α hα
  let d := NativeCondensedModule.localClosedPointDegree D X₀ x
  have hq : (0 : ℝ) < D.q := by
    rw [← D.card_base]
    exact_mod_cast (Nat.card_pos : 0 < Nat.card D.k₀)
  let := (X₀.hom.residueFieldAlgebraMap x.val).toAlgebra
  have := (closedPoint_iff_residueField_trdeg_zero_and_finite X₀.hom x.val).2.1.mp x.prop
  have : Finite (X₀.left.residueField x.val) := Module.finite_of_finite D.k₀
  have hc : Nat.card (X₀.left.residueField x.val) = D.q ^ d := by
    simpa only [d, NativeCondensedModule.localClosedPointDegree, D.card_base] using
      (Module.natCard_eq_pow_finrank (K := D.k₀) (V := X₀.left.residueField x.val))
  have hnorm : ‖iota α.down‖ = 1 := by
    calc
      ‖iota α.down‖ = ‖iota b‖ ^ d * ‖iota β.down‖ := by
        rw [hαβ, map_mul, map_pow, norm_mul, norm_pow]
      _ = ((D.q : ℝ) ^ (-w / 2)) ^ d * ((D.q : ℝ) ^ d) ^ (w / 2) := by
        rw [hb, hpure x i hi β hβ, hc, Nat.cast_pow]
      _ = 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le,
          ← Real.rpow_natCast (D.q : ℝ) d, ← Real.rpow_mul hq.le,
          ← Real.rpow_add hq]
        convert Real.rpow_zero (D.q : ℝ) using 1 <;> ring
  simpa using hnorm

end WeilConjectures.NativeEnvelope
