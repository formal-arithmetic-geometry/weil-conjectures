module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

universe u v

namespace RingHom

/-! # Dimension and maximal ideals under integral extensions

Source: Stacks Project, Algebra, Lemma Tag 00OJ (lemma-integral-dim-up),
with Lemmas Tags 00GT and 00OI (blueprint: lem-weil-pbc-integral-extension-dimension).
-/

/-- An integral ring map does not increase Krull dimension, and maximal ideals contract
 to maximal ideals. Source: Stacks Project, Algebra, Lemma Tag 00OJ
 (blueprint: lem-weil-pbc-integral-extension-dimension).

Proof: For a strict chain of prime ideals in the target, contract each prime along the
ring map. Integrality and incomparability make the contracted inclusions strict, so the
chain length is bounded by the Krull dimension of the source. For a maximal ideal in the
target, the integral-extension maximal-contraction theorem makes its contraction maximal.
-/
theorem integralExtensionDimension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R ∧
      ∀ (I : Ideal S), I.IsMaximal → (I.comap f).IsMaximal := by
  sorry

end RingHom
