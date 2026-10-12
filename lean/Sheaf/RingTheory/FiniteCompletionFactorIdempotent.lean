/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Algebra.Ring.Idempotent
import Sheaf.RingTheory.CompletionFiniteExtensionDecomposition

/-!
# The idempotent selecting a finite-algebra completion factor

Source: Stacks Project, Tag 07NC, the finite product decomposition and its selected factor.
-/

@[expose] public section

universe u v

namespace Algebra

/-- Select the finite completion factor before transferring it to the larger tensor.

Source: Stacks Project, Algebra, proof of Lemma Tag 07NC, the finite-algebra product
and the unit on the selected factor
(blueprint: lem-weil-pbc-finite-completion-factor-idempotent).

Proof: put q' = q contracted to S'. Clearing powers of g identifies S' localized
at q' with S localized at q, since g lies outside the primes. The isomorphism
identifies maximal ideals and their powers. The quotient isomorphisms commute
with reduction and give an isomorphism alpha of completions. This isomorphism
agrees on the images of S' with the natural map to the completion of S_q.
Apply completion_finite_extension_decomposition to S' at p. The ideal q' is prime and lies
over p, so it indexes one of the product factors. Compare the factor's map theta
from the completion of R_p with psi: on each nth quotient represent the coordinate
of x by a in R_p, apply the levelwise formulas and the local-ring square. Their
coordinates agree after alpha, hence alpha(theta(x)) = psi(x). Consequently the
specified phi composed with the tensor inclusion j is alpha composed with this
factor projection: check on x tensor y by multiplying x tensor 1 and 1 tensor y.
Let e be the inverse image of the tuple equal to 1 at q' and 0 elsewhere under
the finite product equivalence. It is idempotent, maps to 1 under phi j, and its
multiplication kills exactly the kernel of that factor projection. The image of
gamma at q' is a unit: g is outside q', hence is a unit in the local ring and
in its completion. Let v be the inverse image of the tuple equal to its inverse
at q' and 0 elsewhere. Then v gamma = e. The factor projection is surjective:
for c in the target, take the tuple supported at q' with value alpha inverse(c).
This also proves the asserted surjectivity of phi j. The complementary product
can be empty, and the formulas remain valid in that case. -/
theorem finite_completion_factor_idempotent
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] (q : PrimeSpectrum S)
    (S' : Subalgebra R S) [Module.Finite R S']
    (g : S') (hg : g.1 ∉ q.asIdeal)
    (haway : Function.Bijective (Localization.awayMap S'.val.toRingHom g)) :
    let p : Ideal R := q.comap (algebraMap R S)
    let Rp := Localization.AtPrime p
    let Sq := Localization.AtPrime q.asIdeal
    let Ip := IsLocalRing.maximalIdeal Rp
    let Iq := IsLocalRing.maximalIdeal Sq
    let Rph := AdicCompletion Ip Rp
    let Sqh := AdicCompletion Iq Sq
    let f : Rp →+* Sq := Localization.localRingHom p q.asIdeal (algebraMap R S) rfl
    let T := TensorProduct R Rph S'
    let U := TensorProduct R Rph S
    let j := (TensorProduct.map (AlgHom.id R Rph) S'.val).toRingHom
    let γ := TensorProduct.tmul R (1 : Rph) g
    ∀ (ψ : Rph →+* Sqh),
      (∀ (n : ℕ) (x : Rph) (a : Rp),
        AdicCompletion.evalₐ Ip n x = Ideal.Quotient.mk (Ip ^ n) a →
        AdicCompletion.evalₐ Iq n (ψ x) = Ideal.Quotient.mk (Iq ^ n) (f a)) →
      ∀ (φ : U →+* Sqh),
        (∀ (x : Rph) (y : S), φ (TensorProduct.tmul R x y) =
          ψ x * algebraMap Sq Sqh (algebraMap S Sq y)) →
        ∃ e v : T, IsIdempotentElem e ∧ v * γ = e ∧ φ (j e) = 1 ∧
          Function.Surjective (φ.comp j) ∧ (∀ t, φ (j t) = 0 → e * t = 0) := by sorry

end Algebra
