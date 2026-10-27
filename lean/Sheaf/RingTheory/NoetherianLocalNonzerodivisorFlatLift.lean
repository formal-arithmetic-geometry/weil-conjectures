module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Flat.Tensor

/-!
# Lifting flatness through a target nonzerodivisor

Source: Stacks Project, Divisors, Tag 062U (lemma-flat-at-x), the algebraic
kernel-and-Nakayama argument, also used in Tag 063T. Only the target ring needs to
be Noetherian and local; the base ring is arbitrary.
(blueprint: lem-sfb-noetherian-local-nonzerodivisor-flat-lift)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Module

/-- Flatness over an arbitrary commutative base lifts through a nonzerodivisor in the
maximal ideal of a Noetherian local target. Source: Stacks Project, Divisors, Tag 062U,
the algebraic argument in the proof of lemma-flat-at-x, used repeatedly in Tag 063T.
(blueprint: lem-sfb-noetherian-local-nonzerodivisor-flat-lift)

Proof:
1. For a finitely generated ideal I of A, put P = I tensor_A C and let mu : P -> C
   be multiplication. The tensors a_i tensor 1 of a finite generating set of I
   generate P over C. Thus K = ker(mu) is finite over C, by
   lem-weil-pbc-noetherian-submodule-finite.
2. Set D = C/tC. By lem-weil-pbc-tensor-right-exact, the map
   q : P -> I tensor_A D is surjective with kernel tP. Flatness of D over A
   (def-weil-pbc-flat-ring-map) makes the multiplication map
   mu_bar : I tensor_A D -> D injective. On pure tensors, and hence on all of P,
   mu_bar composed with q equals the quotient map composed with mu.
3. For k in K, injectivity of mu_bar implies q(k) = 0, so k = t*y.
   Then t*mu(y) = 0; regularity of t on C gives mu(y) = 0. Thus y lies in K
   and K = tK. No regularity of t on P is required.
4. Since (t) lies in the maximal ideal, which is the Jacobson radical of C,
   lem-weil-pbc-nakayama-jacobson gives K = 0. Hence I tensor_A C -> C is
   injective for every finitely generated ideal I of A. Apply
   lem-weil-pbc-flat-fg-ideal-criterion to conclude. None of these steps needs
   Noetherianity or locality of A, or a finiteness property of A -> C.
-/
theorem flat_of_noetherian_local_nonzerodivisor_quotient
    (A : Type u) (C : Type v) [CommRing A] [CommRing C]
    [Algebra A C] [IsNoetherianRing C] [IsLocalRing C]
    (t : C) (ht_mem : t ∈ IsLocalRing.maximalIdeal C)
    (ht_reg : ∀ c : C, t * c = 0 → c = 0)
    (hquot : Module.Flat A (C ⧸ Ideal.span {t})) : Module.Flat A C := by
  sorry

end Module
