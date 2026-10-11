/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Descent of extensions with an ideal-power torsion quotient

Source: Stacks Project, Dualizing Complexes, Lemma 05EH (blueprint:
lem-weil-pbc-torsion-extension-flat-descent).

Base change is written `S ⊗[R] M`, as in Mathlib's tensor product API; this is
canonically the source's `M ⊗[R] S`. Exactness is expressed by injectivity,
`Function.Exact`, and surjectivity of the two linear maps.
-/

universe u v w x y

open TensorProduct

namespace LinearMap

/--
Source: Stacks Project, Dualizing Complexes, Lemma 05EH, in the form used in
the proof of More on Algebra, Proposition 05ER
(blueprint: lem-weil-pbc-torsion-extension-flat-descent).

The hypotheses say that `S` is flat over `R`, that `R/I → S/IS` is an
isomorphism, and that `Q` is `I`-power torsion.  The conclusion constructs an
extension of `Q` by `N` whose base change is the given extension, together
with an isomorphism preserving both end maps.

Proof:
1. Choose a surjection `P = ⨁ j, R/I^(n j) → Q` with torsion kernel `K`
   (lem-weil-pbc-torsion-cyclic-presentation). Flat tensor exactness and tensor
   right exactness identify `K_S` with the kernel of `P_S → Q_S`.
2. Pull back the given extension to `P_S`: its middle module is the pairs
   `(m,x)` with `π(m) = p_S(x)`. Its injection sends `n` to `(ι(n),0)`.
   Descend each cyclic summand by lem-weil-pbc-cyclic-extension-flat-descent,
   then assemble them by lem-weil-pbc-direct-sum-extension-assembly. Obtain
   an extension `N → E_P → P` and an extension isomorphism `α : (E_P)_S ≃ T`.
3. The kernel has the canonical lift `z ↦ (0,k_S(z))` into `T`. Transport
   this through `α`. Torsion Hom comparison (lem-weil-pbc-torsion-hom-flat-comparison)
   descends it to `s : K → E_P`; injectivity of the same comparison gives
   `b s = k`. Thus `s` is injective and its image meets the image of `N` trivially.
4. Put `E = E_P/s(K)` (def-weil-pbc-quotient-module). The injection of `N`
   stays injective by step 3. The map `p b` kills `s(K)` and induces `q`.
   Surjectivity follows from that of `p` and `b`. If `q([e]) = 0`, write
   `b(e) = k(z)`; then `e-s(z)` lies in the image of `N`, proving exactness.
5. Flat tensor exactness and tensor right exactness identify `E_S` with
   `(E_P)_S/s_S(K_S)`. Under `α` the submodule being quotiented is precisely
   the kernel of the surjective projection `T → M'`. This gives `θ`.
   The formula `α(a_S(n)) = (ι(n),0)` gives `θ j_S = ι`; the defining
   equation of `T` gives `π θ = q_S`, as required. -/
theorem exists_torsion_extension_flat_descent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (_hflat : (algebraMap R S).Flat) (I : Ideal R) (_hI : I.FG)
    (_hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
        Ideal.le_comap_map))
    {N : Type w} [AddCommGroup N] [Module R N]
    {Q : Type x} [AddCommGroup Q] [Module R Q]
    (_hQ : ∀ x : Q, ∃ n : ℕ, 1 ≤ n ∧ ∀ r ∈ I ^ n, r • x = 0)
    {M' : Type y} [AddCommGroup M'] [Module S M']
    (ι : S ⊗[R] N →ₗ[S] M')
    (π : M' →ₗ[S] S ⊗[R] Q)
    (_hι : Function.Injective ι) (_hιπ : Function.Exact ι π)
    (_hπ : Function.Surjective π) :
    ∃ (E : Type (max u w x)) (_ : AddCommGroup E) (_ : Module R E)
      (j : N →ₗ[R] E) (q : E →ₗ[R] Q),
      Function.Injective j ∧ Function.Exact j q ∧ Function.Surjective q ∧
      ∃ θ : S ⊗[R] E ≃ₗ[S] M',
        θ.toLinearMap.comp (j.baseChange S) = ι ∧
        π.comp θ.toLinearMap = q.baseChange S := by
  sorry

end LinearMap
