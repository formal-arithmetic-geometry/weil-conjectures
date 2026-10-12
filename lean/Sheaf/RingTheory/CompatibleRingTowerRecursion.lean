module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Algebra.Algebra.Hom

@[expose] public section

universe u v w

namespace IsLocalRing

/-- Source: Stacks Project, Algebra, Lemma 10.159.1 (Tag 03C3), fourth proof paragraph.
(blueprint: new-compatible-ring-tower-recursion)

Proof: Choose a well-order on I and a base stage from hbase. Use ordinary well-founded
recursion on a fixed type of records. A record stores its stage carrier, ring and
R-algebra structures, its map to K, and, for every index of I, an incoming algebra map
with its domain carrier and structures. At index i, test whether the earlier records
form a coherent diagram: their incoming-map domains must agree with the stored earlier
stages, their maps must satisfy the identity and composition laws, and their maps to K
must commute. If they do, and there are predecessors, apply hstep to that diagram on
the strict initial segment and x = q i. Store the resulting stage and cocone maps. If
there are no predecessors, apply hstep to the singleton base diagram and x = q i.
Fill unused incoming-map entries with the identity of the new stage. If the earlier
records are incoherent, use the base record as a default. Fix these choices before
recursing. All records form a type in universe w+1 (or larger to hold the parameters),
so well-founded recursion applies without increasing any carrier's universe.
By well-founded induction the default branch is never used. The cocone equations give
composition with all preceding transitions and compatibility with K; identities give
the diagonal maps. The domains stored in the new record are exactly the previously
chosen carriers. Thus the recursively chosen records give one coherent diagram.
The new stage satisfies P and contains q i by hstep. This also covers finite orders,
orders with limit stages, and the empty order (where the final diagram is empty).
Choices are made inside this existence proof, not used to define any ring. -/
theorem exists_compatible_ring_tower
    (R : Type u) [CommRing R] (K : Type v) [CommRing K]
    (I : Type w) (q : I → K)
    (P : ∀ (A : Type w) [CommRing A] [Algebra R A], (A →+* K) → Prop)
    (hbase : ∃ (A : Type w) (_ : CommRing A) (_ : Algebra R A)
      (ψ : A →+* K), P A ψ)
    (hstep : ∀ (J : Type w) [LinearOrder J] [Nonempty J]
      (A : J → Type w) [∀ j, CommRing (A j)] [∀ j, Algebra R (A j)]
      (f : ∀ i j, i ≤ j → A i →ₐ[R] A j)
      [DirectedSystem A (fun i j h ↦ f i j h)]
      (ψ : ∀ j, A j →+* K),
      (∀ i j h a, ψ j (f i j h a) = ψ i a) →
      (∀ j, P (A j) (ψ j)) → ∀ x : K,
      ∃ (B : Type w) (_ : CommRing B) (_ : Algebra R B) (φ : B →+* K)
        (g : ∀ j, A j →ₐ[R] B),
        (∀ i j h a, g j (f i j h a) = g i a) ∧
        (∀ j a, φ (g j a) = ψ j a) ∧ P B φ ∧ ∃ b, φ b = x) :
    ∃ (_ : LinearOrder I) (A : I → Type w)
      (_ : ∀ i, CommRing (A i)) (_ : ∀ i, Algebra R (A i))
      (f : ∀ i j, i ≤ j → A i →ₐ[R] A j),
      DirectedSystem A (fun i j h ↦ f i j h) ∧
      ∃ (ψ : ∀ i, A i →+* K),
        (∀ i j h a, ψ j (f i j h a) = ψ i a) ∧
        (∀ i, P (A i) (ψ i)) ∧ (∀ i, ∃ a, ψ i a = q i) := by sorry

end IsLocalRing
