/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import Sheaf.RingTheory.PresentationFittingIdeal
public import WeilConjectures.Mathlib.Algebra.Module.Torsion
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.RingTheory.AffinePrincipalFittingGenerators

/-!
# A free open after removing power torsion

Source: Stacks Project, More on Flatness, Tag 0810, lemma-helper-blowup-affine-space,
last two proof paragraphs, abstracted to an arbitrary ring and prime.
(blueprint: lem-trf-principal-fitting-power-torsion-free-open)

The Fitting conditions use finite generating surjections and the presentation-independent
kernel-row ideals of `LinearMap.presentationFittingIdeal_independence_baseChange`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace LinearMap

/-- A principal rth Fitting ideal at a prime, together with vanishing of the preceding
Fitting ideal after inverting a regular element `a = h * c`, makes the power-torsion
quotient free of rank `r` on a principal open containing that prime.
Source: Stacks Project, More on Flatness, Tag 0810, lemma-helper-blowup-affine-space,
last two proof paragraphs, abstracted to an arbitrary ring and prime.
(blueprint: lem-trf-principal-fitting-power-torsion-free-open)

The existential presentations compute the Fitting ideals on any finite generating
surjections; `lem-trf-fitting-ideal-independence-base-change` makes their values independent
of those choices. The lower Fitting condition is imposed only when `0 < r`.

Proof plan, following the six steps of the node:
1. Localize at `q`. Apply `lem-trf-affine-principal-fitting-generators` over the local
   ring `A_q` to get at most `r` generators modulo the kernel of multiplication by `c/1`.
2. The surjection `P_q → Q_q`, with `Q = P / Γ_(a)(P)`, kills that kernel: if
   `t * c • m = 0` with `t ∉ q`, then `t * a • m = 0` because `a = h * c`.
   Thus its images generate `Q_q`. Clear their denominators and pad to `r` generators.
3. Express the images of finite generators of `P` in terms of these generators in `Q_q`.
   Clear all denominators and the witnesses for equality of fractions. Their finite
   product is `g ∉ q`; the resulting map `π : A_g^r → Q_g` is surjective.
   Empty products are one. If `r = 0`, surjectivity already gives the conclusion.
4. For `r > 0`, identify `Q_a` with `P_a`: power torsion becomes zero after inverting
   `a`, and a fraction mapping to zero has a numerator killed by a power of `a`.
   Inverting also `g` identifies `(Q_g)_a` with `(P_a)_g`.
5. Use `lem-trf-fitting-ideal-independence-base-change` to transport the zero lower
   Fitting ideal to `(P_a)_g`. For the localized surjection `π_a`, its kernel-row
   one-by-one minors are precisely relation coordinates. Every coordinate therefore
   vanishes after inverting `a`, so some power of `a` kills it in `A_g`.
6. Multiplication by `a` stays injective on `A_g`: clear a denominator and cancel `a`
   in `A`. Repeated cancellation kills every relation coordinate from step 5.
   Hence `π` is bijective, and its linear inverse gives `Q_g ≃ₗ[A_g] A_g^r`.
   Localization, power torsion and freeness are the recorded dependency notions.
-/
theorem exists_free_open_quotient_powTorsion_of_principal_fitting
    {A : Type u} [CommRing A] {P : Type v} [AddCommGroup P] [Module A P]
    [Module.Finite A P] (r : ℕ) (a h c : A) (hac : a = h * c)
    (q : Ideal A) [q.IsPrime] (ha : Function.Injective (fun x : A ↦ a * x))
    (hfit : ∃ (n : ℕ)
      (π : (Fin n → Localization.AtPrime q) →ₗ[Localization.AtPrime q]
        LocalizedModule q.primeCompl P),
      Function.Surjective π ∧ π.presentationFittingIdeal r =
        Ideal.span ({algebraMap A (Localization.AtPrime q) c} : Set (Localization.AtPrime q)))
    (hlower : 0 < r → ∃ (n : ℕ)
      (π : (Fin n → Localization.Away a) →ₗ[Localization.Away a] LocalizedModule.Away a P),
      Function.Surjective π ∧ π.presentationFittingIdeal (r - 1) = ⊥) :
    ∃ g : A, g ∉ q ∧ Nonempty
      (LocalizedModule.Away g (P ⧸ Submodule.powTorsion A P a) ≃ₗ[Localization.Away g]
        (Fin r → Localization.Away g)) := by
  sorry

end LinearMap
