/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.RingTheory.FormalGlueingData
public import Sheaf.RingTheory.CoverModuleExact

/-!
# Compatible tuples induced by canonical morphisms

Source: Stacks Project, More on Algebra, Lemmas 05EK and 05EM.
-/

@[expose] public section

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace FormalGlueing

/-- The image of an input under the components of a canonical morphism is a compatible
formal glueing tuple. This is a kernel calculation, with no flatness assumption and no
assertion of existence of a preimage in N.
Source: Stacks Project, More on Algebra, Remark 05EL and the complex preceding Lemma 05EK.
(blueprint: lem-weil-pbc-formal-glueing-morphism-tuple).
Proof: transport the prime and chart components along the given object equalities.
Evaluate prime compatibility on (1 tensor m)/1. The canonical comparison formula
identifies the two sides with the comparison of the localized prime value and
1 tensor c_i(m/1). The comparison is injective, so the prime differences vanish.
Evaluate overlap compatibility on (m/1)/1. The canonical swap fixes this double
localization of m, so swap(n_i/1) = n_j/1 for n_i = c_i(m/1).
Write n_i = x/f_i^a and n_j = y/f_j^b. The swap formula identifies the left side
with (x/1)/f_i^a. Clearing the outer f_i denominator gives a power f_i^c
annihilating x/1 - f_i^a y/f_j^b in N_fj. Clearing the inner f_j denominator gives
a power f_j^d annihilating f_i^c(f_j^b x - f_i^a y) in N.
The difference of the images in N_(fi*fj) has numerator
f_i^b f_j^a(f_j^b x - f_i^a y) and denominator (f_i*f_j)^(a+b).
Multiplication by (f_i*f_j)^(c+d) annihilates that numerator. Thus all overlap
differences vanish as well. Extensionality of products and functions gives beta = 0.
Empty chart families, zero denominators and zero modules are included, since this
argument uses localized equality criteria and never cancels a scalar in N. -/
theorem canonical_tuple_compatible {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (M N : ModuleCat.{max u v w} R)
    (X Y : Data.{u, v, max u v w} φ f)
    (hX : X.M' = extend φ M ∧
      (∀ i, X.M i = ModuleCat.of (Localization.Away (f i))
        (LocalizedModule.Away (f i) M)) ∧
      (∀ i, HEq (X.alpha i).toLinearMap (compare φ (f i) M)) ∧
      (∀ i j, HEq (X.alpha_overlap i j).toLinearMap (swap (f i) (f j) M)))
    (hY : Y.M' = extend φ N ∧
      (∀ i, Y.M i = ModuleCat.of (Localization.Away (f i))
        (LocalizedModule.Away (f i) N)) ∧
      (∀ i, HEq (Y.alpha i).toLinearMap (compare φ (f i) N)) ∧
      (∀ i j, HEq (Y.alpha_overlap i j).toLinearMap (swap (f i) (f j) N)))
    (z : X ⟶ Y)
    (p : extend φ M →ₗ[S] extend φ N)
    (c : ∀ i, localize (f i) M →ₗ[R] localize (f i) N)
    (hp : HEq z.prime p) (hc : ∀ i, HEq (z.chart i) (c i)) :
    letI : Algebra R S := φ.toAlgebra
    let η : N →ₗ[R] S ⊗[R] N := TensorProduct.mk R S N 1
    let ρ := fun (a h : R) (ha : a ∣ h) ↦
      IsLocalizedModule.lift (Submonoid.powers a)
        (LocalizedModule.mkLinearMap (Submonoid.powers a) N)
        (LocalizedModule.mkLinearMap (Submonoid.powers h) N)
        (RingTheory.localizationAway_map_units_of_dvd (M := N) a h ha)
    let β : (S ⊗[R] N) × (∀ i : Fin t, LocalizedModule.Away (f i) N) →
        (∀ i : Fin t, LocalizedModule.Away (f i) (S ⊗[R] N)) ×
          (∀ i j : Fin t, LocalizedModule.Away (f i * f j) N) :=
      fun q ↦
        (fun i ↦ LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (S ⊗[R] N) q.1 -
          IsLocalizedModule.map (Submonoid.powers (f i))
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) N)
            (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (S ⊗[R] N)) η (q.2 i),
         fun i j ↦ ρ (f i) (f i * f j) (dvd_mul_right (f i) (f j)) (q.2 i) -
          ρ (f j) (f i * f j) (dvd_mul_left (f j) (f i)) (q.2 j))
    ∀ m : M, β (p ((1 : S) ⊗ₜ[R] m), fun i ↦ c i (LocalizedModule.mk m 1)) = 0 := by
  sorry

end FormalGlueing
