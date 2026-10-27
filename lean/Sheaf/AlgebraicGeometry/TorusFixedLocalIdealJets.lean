module

public import Sheaf.RingTheory.HopfActionModuleData
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Local fixed ideals and rational jets of a split torus

Source: Milne, Algebraic Groups (2017), Lemma 13.4, p.255, and the proof of
Lemma 13.6, p.256 (blueprint: lem-sfb-torus-fixed-local-ideal-jets).

We use affine coordinates: the torus has Laurent algebra k[Z^r], its action is
an algebra coaction, and the fixed closed subscheme is Spec(B/K). The local
rings are actual localizations, and every comparison is normalized on B.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace AlgebraicGeometry.TorusFixedJets

/-- The Laurent coordinate algebra of the rank-r split torus, including rank zero.
Source: Milne, Chapter 12, and Lemma 13.4, p.255
(blueprint: lem-sfb-torus-fixed-local-ideal-jets). -/
abbrev Coordinates (k : Type u) [Field k] (r : ℕ) := AddMonoidAlgebra k (Fin r → ℤ)

/-- The prime defined by a rational point of an affine scheme.
Source: Milne, Lemma 13.4, p.255
(blueprint: lem-sfb-torus-fixed-local-ideal-jets). -/
def pointPrime {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    (x : B →ₐ[k] k) : PrimeSpectrum B :=
  ⟨RingHom.ker x, RingHom.ker_isPrime x⟩

/-- The actual local ring of Spec B at the rational point.
Source: Milne, Lemma 13.4, p.255
(blueprint: lem-sfb-torus-fixed-local-ideal-jets). -/
abbrev LocalRing {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    (x : B →ₐ[k] k) := Localization.AtPrime (pointPrime x).asIdeal

/-- Evaluation of the affine coaction at an algebra-valued torus point.
Source: Milne, Chapter 1(f), p.26, and Lemma 13.4, p.255
(blueprint: lem-sfb-torus-fixed-local-ideal-jets). -/
def evaluate {k C E D : Type u} [Field k] [CommRing C] [CommRing E]
    [CommRing D] [Algebra k C] [Algebra k E] [Algebra k D]
    (c : E →ₐ[k] E ⊗[k] C) (q : E →ₐ[k] D) (t : C →ₐ[k] D) : E →ₐ[k] D :=
  (Algebra.TensorProduct.productMap q t).comp c

/-- The local difference ideal, with generators restricted to the maximal ideal.
Source: Milne, Lemma 13.4, p.255
(blueprint: lem-sfb-torus-fixed-local-ideal-jets). -/
def differenceIdeal {k A C : Type u} [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [CommRing C] [Algebra k C]
    (τ : (C →ₐ[k] k) → (A ≃ₐ[k] A)) : Ideal A :=
  Ideal.span {a | ∃ (t : C →ₐ[k] k) (f : IsLocalRing.maximalIdeal A),
    a = τ t f - f}

/-- The order-N local jet algebra.
Source: Milne, proof of Lemma 13.6, p.256
(blueprint: lem-sfb-torus-fixed-local-ideal-jets). -/
abbrev Jet {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    (x : B →ₐ[k] k) (N : ℕ) := LocalRing x ⧸ IsLocalRing.maximalIdeal (LocalRing x) ^ N

/-- The canonical map from the local ring to its order-N jets.
Source: Milne, proof of Lemma 13.6, p.256
(blueprint: lem-sfb-torus-fixed-local-ideal-jets). -/
def jetMap {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    (x : B →ₐ[k] k) (N : ℕ) : LocalRing x →ₐ[k] Jet x N :=
  Ideal.Quotient.mkₐ k _

/-- The ideal m/m^N as its actual image inside the jet algebra.
Source: Milne, proof of Lemma 13.6, p.256
(blueprint: lem-sfb-torus-fixed-local-ideal-jets). -/
def JetIdeal {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    (x : B →ₐ[k] k) (N : ℕ) : Submodule k (Jet x N) :=
  ((IsLocalRing.maximalIdeal (LocalRing x)).map (jetMap x N)).restrictScalars k

/-- The canonical quotient coordinate of the fixed subscheme.
Source: Milne, Lemma 13.4, p.255
(blueprint: lem-sfb-torus-fixed-local-ideal-jets). -/
def quotientPoint {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    (K : Ideal B) (x : (B ⧸ K) →ₐ[k] k) : B →ₐ[k] k :=
  x.comp (Ideal.Quotient.mkₐ k K)

/-- The fixed local ideal and the rational coactions on all finite jets, including
compatibility with evaluation, the ideal subrepresentation, and cotangent reduction.

Source: Milne, Lemma 13.4, p.255, and proof of Lemma 13.6, p.256
(blueprint: lem-sfb-torus-fixed-local-ideal-jets).

Proof:
1. The affine product and algebra tensor pushout identify the action with rho.
   The Laurent Hopf algebra has comultiplication z^a ↦ z^a tensor z^a
   and counit z^a ↦ 1, so the algebra coaction laws are the action diagrams.
2. Expand rho(b)-b tensor 1 in Laurent coefficients. Their ideal represents
   exactly the fixed functor: test the universal torus point over D[Z^r].
   Apply the given fixed-functor condition to B/K and to the coefficient
   quotient to identify their ideals, without taking radicals.
3. The algebraically closed field is infinite. Apply
   lem-sfb-laurent-vector-evaluation-test to the quotient of B by the ideal
   of rational-point differences. This identifies that ideal with the
   Laurent coefficient ideal, even when B is not reduced.
4. Localize at ker(x). The evaluations preserve this prime. Their localizations
   are the automorphisms tau, uniquely normalized on B. Subtract x(b) to
   replace b by an element of the maximal ideal. For a fraction b/s,
   its difference is (s(t*b-b)-b(t*s-s))/(s t*s). Thus J=K A.
   Use lem-weil-pbc-spec-map-stalk-localization and
   lem-weil-pbc-localization-at-prime-of-quotient to obtain the displayed
   isomorphism, with exactly the closed-immersion quotient map.
5. Choose finitely many algebra generators of B, subtract their values at x,
   and span B/p^N by their monomials of total degree less than N.
   Each denominator s outside p has invertible constant term; its inverse
   modulo p^N is the finite geometric sum. Hence B/p^N = A/m^N and the
   latter is finite dimensional, including when there are no generators.
6. Fixedness of x implies rho(p) is contained in p tensor C. Multiplicativity
   preserves p^N. Reduce Laurent coefficients and transport the coaction
   along B/p^N = A/m^N. This proves both coaction laws, evaluation at tau,
   and stability of m/m^N. The same coefficient reduction gives the
   surjective equivariant map to m/m^2; for N=2 this is the identity.
   No regularity or smoothness enters any step. -/
theorem torus_fixed_local_ideal_jets
    {k B : Type u} [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (r : ℕ)
    (ρ : HopfAction.AlgebraCoaction k (Coordinates k r) B)
    (K : Ideal B)
    (hfixed : ∀ (D : Type u) [CommRing D] [Algebra k D] (q : B →ₐ[k] D),
      K ≤ RingHom.ker q ↔
        ∀ (D' : Type u) [CommRing D'] [Algebra k D'] (f : D →ₐ[k] D')
          (t : Coordinates k r →ₐ[k] D'), evaluate ρ.map (f.comp q) t = f.comp q)
    (x : (B ⧸ K) →ₐ[k] k) :
    ∃ τ : (Coordinates k r →ₐ[k] k) →
        (LocalRing (quotientPoint K x) ≃ₐ[k] LocalRing (quotientPoint K x)),
      (∀ (t : Coordinates k r →ₐ[k] k) (b : B),
        τ t (algebraMap B (LocalRing (quotientPoint K x)) b) =
          algebraMap B (LocalRing (quotientPoint K x))
            (evaluate ρ.map (AlgHom.id k B) ((Algebra.ofId k B).comp t) b)) ∧
      (∃ e : IsLocalRing.ResidueField (LocalRing (quotientPoint K x)) ≃ₐ[k] k,
        ∀ b : B,
          e (IsLocalRing.residue _ (algebraMap B (LocalRing (quotientPoint K x)) b)) =
            quotientPoint K x b) ∧
      differenceIdeal τ ≤ IsLocalRing.maximalIdeal (LocalRing (quotientPoint K x)) ∧
      (∃ e : (LocalRing (quotientPoint K x) ⧸ differenceIdeal τ) ≃ₐ[k] LocalRing x,
        ∀ b : B,
          e (Ideal.Quotient.mk _ (algebraMap B (LocalRing (quotientPoint K x)) b)) =
            algebraMap (B ⧸ K) (LocalRing x) (Ideal.Quotient.mk K b)) ∧
      ∃ c : (N : ℕ) → HopfAction.AlgebraCoaction k (Coordinates k r)
          (Jet (quotientPoint K x) N),
        ∀ n : ℕ, 1 ≤ n →
          FiniteDimensional k (Jet (quotientPoint K x) (n + 1)) ∧
          (∀ (t : Coordinates k r →ₐ[k] k) (a : LocalRing (quotientPoint K x)),
            evaluate (c (n + 1)).map (AlgHom.id k _) ((Algebra.ofId k _).comp t)
                (jetMap (quotientPoint K x) (n + 1) a) =
              jetMap (quotientPoint K x) (n + 1) (τ t a)) ∧
          (∃ d : JetIdeal (quotientPoint K x) (n + 1) →ₗ[k]
              JetIdeal (quotientPoint K x) (n + 1) ⊗[k] Coordinates k r,
            HopfAction.Counital k (Coordinates k r) _ d ∧
            HopfAction.Coassociative k (Coordinates k r) _ d ∧
            (JetIdeal (quotientPoint K x) (n + 1)).subtype.rTensor (Coordinates k r) ∘ₗ d =
              (c (n + 1)).map.toLinearMap ∘ₗ
                (JetIdeal (quotientPoint K x) (n + 1)).subtype ∧
            ∃ (d₂ : JetIdeal (quotientPoint K x) 2 →ₗ[k]
                JetIdeal (quotientPoint K x) 2 ⊗[k] Coordinates k r)
              (p : JetIdeal (quotientPoint K x) (n + 1) →ₗ[k]
                JetIdeal (quotientPoint K x) 2),
              HopfAction.Counital k (Coordinates k r) _ d₂ ∧
              HopfAction.Coassociative k (Coordinates k r) _ d₂ ∧
              (JetIdeal (quotientPoint K x) 2).subtype.rTensor (Coordinates k r) ∘ₗ d₂ =
                (c 2).map.toLinearMap ∘ₗ (JetIdeal (quotientPoint K x) 2).subtype ∧
              (∀ a : IsLocalRing.maximalIdeal (LocalRing (quotientPoint K x)),
                (p ⟨jetMap (quotientPoint K x) (n + 1) a,
                  Ideal.mem_map_of_mem _ a.property⟩ : Jet (quotientPoint K x) 2) =
                  jetMap (quotientPoint K x) 2 a) ∧
              Function.Surjective p ∧ p.rTensor (Coordinates k r) ∘ₗ d = d₂ ∘ₗ p) := by
  sorry

end AlgebraicGeometry.TorusFixedJets
