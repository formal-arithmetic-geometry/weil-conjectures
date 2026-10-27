/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Topology.ProfiniteCechTuples
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Topology.InverseLimitCechPrimitive
import Sheaf.Topology.FiniteCoefficientCechPrimitiveLift
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Continuous Cech exactness with finite p-adic field coefficients

Source: Bhatt–Scholze, The pro-etale topology for schemes, Lemma 4.3.9(2)–(4), p. 33,
with trivial group, expanded by the DAG into an explicit continuous-function assertion
(blueprint: lem-sfb-normed-scalar-profinite-cech-exact).

The equations below are the pointwise alternating differentials on continuous cochains.
The coefficient topology is the spectral norm topology, with no local constancy condition.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Profinite

private theorem integral_cech_exact (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S T : Profinite.{v}) (q : C(T, S)) (hq : Function.Surjective q) (n : ℕ)
    (h : @ContinuousMap (scalarCechTuples q (n + 2))
      (Padic.coefficientExtensionIntegers l E) inferInstance
      (Padic.coefficientExtensionIntegersTopology l E))
    (hh : ∀ x : scalarCechTuples q (n + 3),
      ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • h (scalarCechDelete q (n + 2) j x) = 0) :
    ∃ g : @ContinuousMap (scalarCechTuples q (n + 1))
        (Padic.coefficientExtensionIntegers l E) inferInstance
        (Padic.coefficientExtensionIntegersTopology l E),
      ∀ x : scalarCechTuples q (n + 2),
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • g (scalarCechDelete q (n + 1) j x) = h x := by
  classical
  let : NormedField E := spectralNorm.normedField (Padic l) E
  let O := Padic.coefficientExtensionIntegers l E
  let : TopologicalSpace O := Padic.coefficientExtensionIntegersTopology l E
  let A := fun m : ℕ ↦ Padic.coefficientExtensionRing l E (m + 1)
  let : ∀ m, Finite (A m) := fun m ↦ Padic.finite_coefficientExtensionRing l E (m + 1)
    (Nat.le_add_left 1 m)
  let : ∀ m, TopologicalSpace (A m) := fun _ ↦ ⊥
  let : ∀ m, DiscreteTopology (A m) := fun _ ↦ ⟨rfl⟩
  let p := fun m ↦ (Padic.coefficientExtensionTransition l E (m + 1)).toAddMonoidHom
  have hp : ∀ m, Function.Surjective (p m) := fun m ↦
    Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))
  let L := Padic.coefficientExtensionPositiveLimit l E
  let : TopologicalSpace L := Padic.coefficientExtensionPositiveLimitTopology l E
  obtain ⟨⟨e, he, hhome⟩, _⟩ := Padic.coefficientExtension_integers_profinite_tower.{u, 0} l E
  let F : C(scalarCechTuples q (n + 2),
      {a : ∀ m, A m // ∀ m, p m (a (m + 1)) = a m}) :=
    ⟨fun x ↦ ⟨(e (h x)).val, fun m ↦
      (Subring.mem_iInf.mp (e (h x)).property m : _)⟩, by
      apply Continuous.subtype_mk
      exact continuous_induced_rng.mp (hhome.continuous.comp h.continuous)⟩
  have hF (m : ℕ) (x : scalarCechTuples q (n + 3)) :
      ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val •
        (F (scalarCechDelete q (n + 2) j x)).val m = 0 := by
    have ht := congrArg (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (m + 1)))
      (hh x)
    simpa only [map_sum, map_zsmul, map_zero, F, ContinuousMap.coe_mk, he] using ht
  let : TopologicalSpace PUnit.{1} := ⊥
  let : DiscreteTopology PUnit.{1} := ⟨rfl⟩
  let c₀ : C(scalarCechTuples q (n + 2), A 0) :=
    ⟨fun x ↦ (F x).val 0,
      (continuous_apply 0).comp (continuous_subtype_val.comp F.continuous)⟩
  obtain ⟨u₁, _, hu₁⟩ := finite_coefficient_cech_primitive_lift S T q hq
    PUnit.{1} (A 0) 0 (fun _ ↦ ⟨0, rfl⟩) (n + 1) (Nat.le_add_left 1 n)
    c₀ (hF 0) 0 (fun _ ↦ Subsingleton.elim _ _)
  obtain ⟨u, hu, _⟩ := exists_inverseLimit_cech_primitive S T q hq A p hp n F hF u₁ hu₁
  let U : C(scalarCechTuples q (n + 1), L) :=
    ⟨fun x ↦ ⟨(u x).val, by
      apply Subring.mem_iInf.mpr
      exact (u x).property⟩, by
      apply continuous_induced_rng.mpr
      change Continuous (fun x ↦ (u x).val)
      exact continuous_subtype_val.comp u.continuous⟩
  let g : C(scalarCechTuples q (n + 1), O) :=
    ⟨fun x ↦ e.symm (U x), (e.toEquiv.continuous_symm_iff.mpr hhome.isOpenMap).comp U.continuous⟩
  refine ⟨g, fun x ↦ e.injective ?_⟩
  apply Subtype.ext
  funext m
  let rho : L →+ A m := (Pi.evalRingHom A m).toAddMonoidHom.comp
    (L.subtype.toAddMonoidHom)
  change rho (e (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
    g (scalarCechDelete q (n + 1) j x))) = rho (e (h x))
  simp only [map_sum, map_zsmul]
  change (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
    rho (e (e.symm (U (scalarCechDelete q (n + 1) j x))))) = rho (e (h x))
  simp only [RingEquiv.apply_symm_apply]
  exact hu m x

/-- Every positive-degree continuous Cech cocycle with finite p-adic field coefficients
is a continuous coboundary. The degree is `n + 1`, so `n = 0` includes degree one.

Source: Bhatt–Scholze, Lemma 4.3.9(2)–(4), p. 33, and its explicit Cech expansion
(blueprint: lem-sfb-normed-scalar-profinite-cech-exact).

Proof: (1) Iterate lem-sfb-finite-quotient-fiber-product to obtain profiniteness of all
finite fibre powers. Coordinate deletions are continuous and the two orders of deleting
coordinates cancel with opposite signs, giving d squared zero. If both spaces are empty,
all cochains vanish. (2) By lem-sfb-finite-valued-cech-cocycle-descent, a finite discrete
coefficient cocycle descends, including its cocycle equation, to a finite surjection.
Choose a section of that finite surjection and insert it as the first coordinate.
The cocycle equation on the resulting tuple says this gives a primitive; pull it back.
(3) Use def-weil-l-adic-coefficient-extension, lem-weil-l-adic-extension-integers-dvr,
lem-weil-valued-dvr-finite-quotients and lem-sfb-integers-profinite-tower: the integers
are the topological inverse limit of their finite uniformizer-power quotients, whose
transition maps are surjective. (4) For an integral cocycle, first solve modulo the
uniformizer. (5) Lift a primitive at one level by a set section of the next finite
quotient map; the difference between its boundary and the next cocycle lies in the
finite kernel and is a cocycle. (6) Apply the finite-coefficient result to this kernel
cocycle and subtract its primitive. This corrects the lift while preserving its
reduction. Induction gives compatible primitives, also in degree one.
(7) Reconstruct the integral primitive by the inverse-limit homeomorphism. Its boundary
is the given cocycle because they agree in every finite quotient. (8) Compactness bounds
the image of an E-valued cocycle, so multiplication by a single uniformizer power makes
it integral. Solve there and divide the primitive by that same scalar. All constructed
cochains are continuous; none is required to be locally constant. -/
theorem normedScalarProfiniteCech_exact (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S T : Profinite.{v}) (q : C(T, S)) (hq : Function.Surjective q) (n : ℕ)
    (f : @ContinuousMap (scalarCechTuples q (n + 2)) E inferInstance
      (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace)
    (hf : ∀ x : scalarCechTuples q (n + 3),
      ∑ j : Fin (n + 3), (-1 : E) ^ j.val * f (scalarCechDelete q (n + 2) j x) = 0) :
    ∃ g : @ContinuousMap (scalarCechTuples q (n + 1)) E inferInstance
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace,
      ∀ x : scalarCechTuples q (n + 2),
        ∑ j : Fin (n + 2), (-1 : E) ^ j.val * g (scalarCechDelete q (n + 1) j x) = f x := by
  classical
  let : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField (Padic l) E
  have hclosed : IsClosed {t : Fin (n + 2) → T | ∀ i j, q (t i) = q (t j)} :=
    by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_eq
        (q.continuous.comp (continuous_apply i)) (q.continuous.comp (continuous_apply j))
  have : CompactSpace (scalarCechTuples q (n + 2)) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  obtain ⟨R, hR, hbound⟩ := (isCompact_range f.continuous).isBounded.exists_pos_norm_le
  obtain ⟨a, ha, haR⟩ := NormedField.exists_norm_lt E (inv_pos.mpr hR)
  have ha0 : a ≠ 0 := norm_pos_iff.mp ha
  have hO : ∀ x : E, x ∈ Padic.coefficientExtensionIntegers l E ↔ ‖x‖ ≤ 1 :=
    (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec.1
  let O := Padic.coefficientExtensionIntegers l E
  let : TopologicalSpace O := Padic.coefficientExtensionIntegersTopology l E
  have hint (x : scalarCechTuples q (n + 2)) : a * f x ∈ O := by
    rw [hO, norm_mul]
    calc
      ‖a‖ * ‖f x‖ ≤ ‖a‖ * R := mul_le_mul_of_nonneg_left
        (hbound _ (Set.mem_range_self x)) (norm_nonneg a)
      _ ≤ 1 := by nlinarith [mul_inv_cancel₀ hR.ne']
  let h : C(scalarCechTuples q (n + 2), O) :=
    ⟨fun x ↦ ⟨a * f x, hint x⟩, (continuous_const.mul f.continuous).subtype_mk _⟩
  have hh (x : scalarCechTuples q (n + 3)) :
      ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • h (scalarCechDelete q (n + 2) j x) = 0 := by
    apply Subtype.ext
    change (O.subtype) (∑ j : Fin (n + 3),
      (-1 : ℤ) ^ j.val • h (scalarCechDelete q (n + 2) j x)) = 0
    simp only [map_sum, map_zsmul]
    simp only [h, ContinuousMap.coe_mk, Subring.subtype_apply, zsmul_eq_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one]
    calc
      ∑ j : Fin (n + 3), (-1 : E) ^ j.val * (a * f (scalarCechDelete q (n + 2) j x)) =
          a * ∑ j : Fin (n + 3), (-1 : E) ^ j.val *
            f (scalarCechDelete q (n + 2) j x) := by
        rw [Finset.mul_sum]
        congr 1
        funext j
        ring
      _ = 0 := by rw [hf, mul_zero]
  obtain ⟨u, hu⟩ := integral_cech_exact l E S T q hq n h hh
  let g : C(scalarCechTuples q (n + 1), E) :=
    ⟨fun x ↦ a⁻¹ * (u x).val,
      continuous_const.mul (continuous_subtype_val.comp u.continuous)⟩
  refine ⟨g, fun x ↦ ?_⟩
  have hu' := congrArg (O.subtype) (hu x)
  simp only [map_sum] at hu'
  simp only [map_zsmul] at hu'
  change (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
    (u (scalarCechDelete q (n + 1) j x)).val) = a * f x at hu'
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] at hu'
  calc
    ∑ j : Fin (n + 2), (-1 : E) ^ j.val * g (scalarCechDelete q (n + 1) j x) =
        a⁻¹ * ∑ j : Fin (n + 2), (-1 : E) ^ j.val *
          (u (scalarCechDelete q (n + 1) j x)).val := by
      simp only [g, ContinuousMap.coe_mk, Finset.mul_sum]
      congr 1
      funext j
      ring
    _ = f x := by rw [hu', inv_mul_cancel_left₀ ha0]

end Profinite
