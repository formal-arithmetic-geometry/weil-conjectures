/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import WeilConjectures.RingTheory.FormallySmoothAdic

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.CohenRingsExist
import WeilConjectures.RingTheory.ExistsLiftOfFieldCharP
import WeilConjectures.RingTheory.FormallySmoothAdicOfFlatClosedFiber
import WeilConjectures.RingTheory.CompleteLocalQuotient

/-! # Equivariant Cohen coefficient extensions and section lifts

Source: ILO, Travaux de Gabber, Exposé IV, 4.3.5–4.3.6, printed p.60,
with 4.1.3–4.1.9 and 4.2.5 (blueprint: lem-per-equivariant-cohen-coefficient-lift).

The section's equivariance is expressed on representatives in `C/(π)`;
its residue-field action is the canonical `IsLocalRing.ResidueField.mapAut`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace IsLocalRing

/-- An equivariant residue section lifts from a formally smooth coefficient DVR.

Source: ILO, Travaux de Gabber, IV 4.3.5–4.3.6, printed p.60,
with IV 4.1.3–4.1.9 and 4.2.5 (blueprint: lem-per-equivariant-cohen-coefficient-lift).

Proof:
1. Let G be the image of H in Aut(k') and F its fixed field. The fixed-field degree
   theorem makes k'/F finite separable. Choose a Cohen ring D for F and its finite
   etale Cohen extension B for k' (lem-per-finite-etale-cohen-extension). Uniqueness
   of lifts of residue automorphisms gives a G-action on B, hence an H-action.
2. Choose a Cohen ring A for k0. Perfect-residue uniqueness
   (lem-per-perfect-cohen-residue-map) lifts the H-action to A and gives compatible
   equivariant local maps A → W and A → B.
3. Form V = W ⊗[A] B. The ramified tensor DVR lemma
   (lem-per-ramified-cohen-tensor-dvr) gives completeness, injectivity, localness,
   flatness, uniformizer π and residue field k'. The formula h(w ⊗ b) = hw ⊗ hb
   respects balancing by step 2 and gives the required action and residue action.
4. The field extension k'/k0 is formally smooth: lift a map across a square-zero
   ideal using the field characteristic-p lifting theorem. The lift is k0-linear
   because every element of k0 is a p-th power and the error has p-th power zero.
   The flat closed-fibre criterion gives adic formal smoothness of V/W.
5. Put I_r = πC ∩ n^r and E_r = C/I_r for r ≥ 1. These ideals are H-stable;
   E_1 = C/πC and E_(r+1) → E_r has square-zero kernel J_r, annihilated by π.
   Starting with s, formal smoothness lifts each map V → E_r to u : V → E_(r+1).
6. For h in H, the difference d_h = h u h⁻¹ - u takes values in J_r, vanishes
   on W, is additive and satisfies the Leibniz rule since J_r² = 0.
   It satisfies the cocycle identity d_(gh) = d_g + g d_h.
7. Set δ = |H|⁻¹ sum_h d_h. It is a W-derivation into J_r. Thus u + δ is
   a unital W-algebra lift, and reindexing the cocycle identity gives
   gδ = δ - d_g, so this lift is equivariant. Iterate to obtain compatible lifts.
8. Completeness identifies C with the limit of the E_r: injectivity follows from
   n-adic separation; compatible representatives are n-adically Cauchy, and
   separation of C/πC ensures their limit still has the prescribed class modulo π.
   The limit gives ψ with exactly the stated reduction and equivariance. Its map
   to k' is V's residue map, so it is local. No injectivity of ψ is needed. -/
theorem exists_equivariant_cohen_coefficient_lift
    (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W]
    [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (p : ℕ) (hp : Nat.Prime p) [CharP (ResidueField W) p]
    (hperfect : Function.Bijective (fun x : ResidueField W ↦ x ^ p))
    (C : Type v) [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    [Algebra W C] [IsLocalHom (algebraMap W C)]
    [IsAdicComplete (maximalIdeal C) C]
    (H : Type w) [Group H] [Finite H]
    (horder : IsUnit (Nat.card H : W))
    (ρW : H →* RingAut W) (ρC : H →* RingAut C)
    (hcompat : ∀ (h : H) (a : W), ρC h (algebraMap W C a) = algebraMap W C (ρW h a))
    (s : ResidueField C →ₐ[W] C ⧸ Ideal.span {algebraMap W C π})
    (hsection : (Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem (maximalIdeal C)).mpr
      (map_nonunit (algebraMap W C) π hπ.not_isUnit))).comp s.toRingHom =
        RingHom.id (ResidueField C))
    (hsequiv : ∀ (h : H) (x : ResidueField C) (c : C),
      Ideal.Quotient.mk (Ideal.span {algebraMap W C π}) c = s x →
        Ideal.Quotient.mk (Ideal.span {algebraMap W C π}) (ρC h c) =
          s (ResidueField.mapAut (ρC h) x)) :
    ∃ (V : Type (max u v)) (_ : CommRing V) (_ : IsDomain V)
      (_ : IsDiscreteValuationRing V) (_ : Algebra W V),
      IsAdicComplete (maximalIdeal V) V ∧
      IsLocalHom (algebraMap W V) ∧ Function.Injective (algebraMap W V) ∧
      maximalIdeal V = Ideal.span {algebraMap W V π} ∧
      Algebra.FormallySmoothAdic W V (maximalIdeal V) ∧
      ∃ (e : (V ⧸ Ideal.span {algebraMap W V π}) ≃ₐ[W] ResidueField C)
        (ρV : H →* RingAut V) (ψ : V →ₐ[W] C),
        (∀ (h : H) (a : W), ρV h (algebraMap W V a) = algebraMap W V (ρW h a)) ∧
        (∀ (h : H) (a : V),
          e (Ideal.Quotient.mk (Ideal.span {algebraMap W V π}) (ρV h a)) =
            ResidueField.mapAut (ρC h)
              (e (Ideal.Quotient.mk (Ideal.span {algebraMap W V π}) a))) ∧
        IsLocalHom ψ.toRingHom ∧
        (∀ (h : H) (a : V), ψ (ρV h a) = ρC h (ψ a)) ∧
        ∀ a : V, Ideal.Quotient.mk (Ideal.span {algebraMap W C π}) (ψ a) =
          s (e (Ideal.Quotient.mk (Ideal.span {algebraMap W V π}) a)) := by
  sorry

end IsLocalRing
