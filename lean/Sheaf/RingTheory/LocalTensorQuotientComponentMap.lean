module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- The quotient tensor product embeds into the product of its local factors.
Source: Stacks Project, Tag 07N9, quotient-product argument.
(blueprint: lem-weil-pbc-local-tensor-quotient-component-map)

The Artinian product decomposition of the finite quotient algebra gives an
injective linear map to the product of local quotient rings.  Its value on a
pure tensor is the expected localized product. -/
theorem tensor_quotient_component_map
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime]
    (n : ℕ) (hn : 0 < n) :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    ∃ φ : ((Localization.AtPrime p ⧸ (m ^ n)) ⊗[R] S) →ₗ[R]
        (∀ q : p.primesOver S,
          (Localization.AtPrime q.1 ⧸ (m ^ n).map
            (Localization.localRingHom p q.1 (algebraMap R S)
              (Ideal.LiesOver.over (P := q.1) (p := p))))) ,
      Function.Injective φ ∧
        ∀ (r : A) (s : S) (q : p.primesOver S),
          φ ((Ideal.Quotient.mk (m ^ n) r) ⊗ₜ[R] s) q =
            Ideal.Quotient.mk ((m ^ n).map
              (Localization.localRingHom p q.1 (algebraMap R S)
                (Ideal.LiesOver.over (P := q.1) (p := p))))
              (Localization.localRingHom p q.1 (algebraMap R S)
                (Ideal.LiesOver.over (P := q.1) (p := p)) r *
                algebraMap S (Localization.AtPrime q.1) s) := by
  sorry

end AdicCompletion
