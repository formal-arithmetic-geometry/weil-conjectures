module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Algebra.Module.LocalizedModule.Basic

import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.LocalRing.Module

/-!
# Vanishing of differentials detected on ordinary algebra fibres

Source: Stacks Project, algebra.tex, Tags 00UV (lemma-unramified), 00RV
(lemma-differentials-base-change), 00RZ (lemma-differentials-finitely-generated), and 00DV
(lemma-NAK); applied in morphisms.tex, Tag 02G8 (lemma-unramified-etale-fibres), part (2)
(blueprint: lem-trf-fibrewise-zero-kahler-differentials).

The fibre ring is Mathlib's `Ideal.Fiber`, with its natural residue-field algebra structure.
This writes the tensor factors as `κ(p) ⊗[R] A`, canonically isomorphic to `A ⊗[R] κ(p)`.
-/

@[expose] public section

universe u v

namespace KaehlerDifferential

/-- For a finite type algebra, vanishing of relative differentials on every ordinary fibre
implies finite generation of the differential module, its vanishing after tensoring with
every residue field and after localizing at every prime, and its global vanishing.

Source: Stacks Project, algebra.tex, Tag 00UV (lemma-unramified), proof of (7)--(9) and
(11), Tags 00RV, 00RZ and 00DV; morphisms.tex, Tag 02G8(2)
(blueprint: lem-trf-fibrewise-zero-kahler-differentials).

Proof:
1. Choose finitely many algebra generators `aᵢ`. The derivation relations express every
   `db` as an A-linear combination of the `daᵢ`: expand a polynomial expression for `b`
   using additivity, Leibniz and the vanishing of differentials of base-ring elements.
   Thus the `daᵢ` generate the differential module M (also for an empty generator family).
2. Fix a prime q of A and contract it to p in R. The fraction map
   `r/s ↦ φ(r)/φ(s)` into κ(q) kills pRₚ and induces κ(p) → κ(q). Multiplication then
   defines the canonical map C = κ(p) ⊗[R] A → κ(q), agreeing with A → κ(q).
3. By lem-weil-pbc-kahler-differentials-base-change (Tag 00RV), C ⊗[A] M is isomorphic
   to Ω[C/κ(p)], via `c ⊗ da ↦ c d(1 ⊗ a)`. The fibre hypothesis makes it zero.
4. Tensor associativity gives M ⊗[A] κ(q) ≅ (C ⊗[A] M) ⊗[C] κ(q): its maps are
   `m ⊗ z ↦ (1 ⊗ m) ⊗ z` and `(c ⊗ m) ⊗ z ↦ m ⊗ ε(c)z`.
   They respect balancing and are inverse on pure tensors. Hence M ⊗[A] κ(q) is zero.
5. Put B = A_q and N = M_q. The fractions `(daᵢ)/1` generate N over B. The maps
   `(m/s) ⊗ z ↦ m ⊗ z/s` and `m ⊗ z ↦ (m/1) ⊗ z` give inverse isomorphisms
   N ⊗[B] κ(q) ≅ M ⊗[A] κ(q). The fraction relation and invertibility of denominators
   in κ(q) give well-definedness. Therefore the residue-field tensor of N is zero.
6. Apply lem-weil-pbc-nakayama-local-generators (Tag 00DV(8)) over the local ring B
   to the finite module N and the empty family. Its images generate the zero residue
   module, so the empty family generates N and N is zero. This holds at every prime q.
7. Apply lem-weil-pbc-linear-map-bijective-at-maximal-localizations to the zero map
   M → 0: its maximal localizations are bijective by step 6. Hence M is zero globally.
   For the zero ring A there are no primes and every unital A-module is already zero. -/
theorem finite_and_vanishing_of_fiber_vanishing
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A]
    (hfib : ∀ (p : Ideal R) [p.IsPrime],
      Subsingleton (KaehlerDifferential p.ResidueField (p.Fiber A))) :
    Module.Finite A (KaehlerDifferential R A) ∧
      (∀ (q : Ideal A) [q.IsPrime],
        Subsingleton (TensorProduct A (KaehlerDifferential R A) q.ResidueField) ∧
          Subsingleton (LocalizedModule q.primeCompl (KaehlerDifferential R A))) ∧
      Subsingleton (KaehlerDifferential R A) := by
  sorry

end KaehlerDifferential
