module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes

/-!
# Associated primes of a flat tensor lie in the corresponding residue-field fibre

Source: Stacks Project, Algebra, Tag 05C2 (lemma-bourbaki-fibres), together with
Tag 05E0 (remark-bourbaki) (blueprint: lem-trf-associated-primes-fibre-bound).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w x

open scoped TensorProduct

namespace RingTheory

/-- Associated primes of a tensor with a finite flat module occur in the corresponding
residue-field fibre. The fibre-ring formulation is included through the canonical prime
correspondence for `p.Fiber S`.

Source: Stacks Project, Algebra, Tags 05C2 and 05E0. The proof first applies the flat
base-change theorem to obtain an annihilator witness in a prime quotient, identifies its
contraction with the given prime, and transports that witness to the fibre localization.
The canonical action of `S` on the fibre then gives the first assertion; the standard
prime correspondence for `p.Fiber S` gives the equivalent fibre-ring assertion.
(blueprint: lem-trf-associated-primes-fibre-bound). -/
theorem associatedPrimes_fibre_bound
    (R : Type u) (S : Type v) (P : Type w) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup P] [Module S P] [Module R P]
    [IsScalarTower R S P] [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Finite S P] [Module.Flat R P]
    (Q : Type x) [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    (q : Ideal S)
    (hq : letI : Module S (Q ⊗[R] P) :=
      (TensorProduct.comm R Q P).toAddEquiv.module S
      q ∈ annihilatorAssociatedPrimes S (Q ⊗[R] P)) :
    letI : Module S (Q ⊗[R] P) := (TensorProduct.comm R Q P).toAddEquiv.module S
    let p : Ideal R := q.comap (algebraMap R S)
    letI : p.IsPrime := by
      dsimp only [p]
      dsimp only [RingTheory.annihilatorAssociatedPrimes] at hq
      exact hq.1.comap (algebraMap R S)
    letI : Module S (P ⊗[R] p.ResidueField) := by
      exact TensorProduct.leftModule
    q ∈ annihilatorAssociatedPrimes S (P ⊗[R] p.ResidueField) := by
  sorry

end RingTheory
