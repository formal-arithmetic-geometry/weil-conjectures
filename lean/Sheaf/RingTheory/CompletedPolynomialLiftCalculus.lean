module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import WeilConjectures.RingTheory.Derivation.CompletionAndLocalization

/-! # Completed polynomial local rings

Source: Stacks, More on Algebra, Tags 07ED, 07NJ, and 07PE.
(blueprint: lem-sfb-completed-polynomial-lift-calculus)

The continuity conditions use the ideal-power neighbourhood bases at zero. For additive maps
these are precisely continuity for the adic topologies. The tensor factors are reversed using
the canonical commutativity isomorphism, so that Mathlib supplies its left-factor B-action.
The image characterization below expresses the B-linear bijection onto continuous derivations
without introducing a second definition of derivation or a choice of its linear structure.
-/

@[expose] public section

universe u v w

open IsLocalRing
open scoped TensorProduct

namespace Algebra

/-- The differential basis, its completed universal derivation, restriction of local maps, and
square-zero lifting for the completion of a polynomial local ring.

Source: Stacks, More on Algebra, Tags 07ED and 07NJ; the shifted-coordinate derivation formula
is Tag 07PE. (blueprint: lem-sfb-completed-polynomial-lift-calculus)

Proof: (1) The polynomial ring and its localization are Noetherian, by finite-type permanence
and localization. The completion is local, with maximal ideal the extension of the original
one. Its quotients agree with those of the local ring, so the original ring is dense.
(2) The polynomial differential basis localizes to the displayed basis b. Completing finite
tuples coordinatewise gives e, with the stated normalization on the dense original module.
(3) Extend each coordinate derivation by Tag 07PE: the nth output coordinate uses the (n+1)st
input coordinate. The ideal-power estimate gives continuity. Density and separation give
uniqueness of the resulting d. (4) A finite module over a complete Noetherian local ring is
complete and separated, by the completion-tensor theorem. (5) A linear map on the base-changed
free module is determined by its values on the basis. Composition with d is a derivation,
and the shifted ideal-power estimate gives continuity. (6) Conversely a continuous derivation
is determined on the dense local polynomial ring by its values on the variables. Separation
of the target module gives equality everywhere. These constructions commute with B-scalars.
(7) A local map P to E induces compatible maps P/p^n to E/m^n. Completeness of E gives its
extension; density and separation give uniqueness. Its residue map is a field map, proving
locality. Restriction is local because the completion map is local. (8) Lift the variable
images through the square-zero surjection. Elements outside q map to units: an inverse modulo
the kernel lifts using (1+j)⁻¹ = 1-j. Localization gives a local lift on P. Step (7) extends it
to the completion; the two maps to B agree by density and separation. This also covers r=0,
zero target modules, and inseparable residue extensions; no residue-field section is chosen.
-/
theorem completedPolynomial_lift_calculus
    (k : Type u) [Field k] (r : ℕ)
    (q : Ideal (MvPolynomial (Fin r) k)) [q.IsMaximal] :
    ∃ (b : Module.Basis (Fin r) (Localization.AtPrime q) (KaehlerDifferential k
      (Localization.AtPrime q)))
      (e : AdicCompletion (maximalIdeal (Localization.AtPrime q)) (KaehlerDifferential k
        (Localization.AtPrime q)) ≃ₗ[(AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q))] (Fin r → (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q))))
      (d : Derivation k (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q)) (Fin r → (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q)))),
      (∀ i : Fin r, b i = KaehlerDifferential.D k (Localization.AtPrime q) (algebraMap (MvPolynomial
        (Fin r) k) (Localization.AtPrime q) (MvPolynomial.X i))) ∧
      (∀ w : (KaehlerDifferential k (Localization.AtPrime q)), ∀ i : Fin r,
        e (AdicCompletion.of (maximalIdeal (Localization.AtPrime q)) (KaehlerDifferential k
          (Localization.AtPrime q)) w) i = (algebraMap (Localization.AtPrime q) (AdicCompletion
          (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q))) (b.repr w i)) ∧
      (∀ n : ℕ, ∃ N : ℕ, ∀ s ∈ maximalIdeal (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q)) ^ N, d s ∈ (maximalIdeal (AdicCompletion (maximalIdeal
        (Localization.AtPrime q)) (Localization.AtPrime q)) ^ n • (⊤ : Submodule (AdicCompletion
        (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)) (Fin r → (AdicCompletion
        (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)))))) ∧
      (∀ a : (Localization.AtPrime q), ∀ i : Fin r, d ((algebraMap (Localization.AtPrime q)
        (AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q))) a) i =
        (algebraMap (Localization.AtPrime q) (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q))) (b.repr (KaehlerDifferential.D k (Localization.AtPrime q) a) i))
        ∧
      (∀ d' : Derivation k (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q)) (Fin r → (AdicCompletion (maximalIdeal (Localization.AtPrime q))
        (Localization.AtPrime q))),
        (∀ n : ℕ, ∃ N : ℕ, ∀ s ∈ maximalIdeal (AdicCompletion (maximalIdeal (Localization.AtPrime
          q)) (Localization.AtPrime q)) ^ N, d' s ∈ (maximalIdeal (AdicCompletion (maximalIdeal
          (Localization.AtPrime q)) (Localization.AtPrime q)) ^ n • (⊤ : Submodule (AdicCompletion
          (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)) (Fin r → (AdicCompletion
          (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)))))) → (∀ a :
          (Localization.AtPrime q), ∀ i : Fin r, d' ((algebraMap (Localization.AtPrime q)
          (AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q))) a) i =
          (algebraMap (Localization.AtPrime q) (AdicCompletion (maximalIdeal (Localization.AtPrime
          q)) (Localization.AtPrime q))) (b.repr (KaehlerDifferential.D k (Localization.AtPrime q)
          a) i)) → d' = d) ∧
      (∀ (B : Type v) [CommRing B] [Algebra k B] [IsLocalRing B]
        [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B]
        [Algebra (AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q))
          B] [IsScalarTower k (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)) B],
        IsLocalHom (algebraMap (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)) B) →
        (∀ n : ℕ, ∃ N : ℕ, ∀ s ∈ maximalIdeal (AdicCompletion (maximalIdeal (Localization.AtPrime
          q)) (Localization.AtPrime q)) ^ N, (algebraMap (AdicCompletion (maximalIdeal
          (Localization.AtPrime q)) (Localization.AtPrime q)) B) s ∈ (maximalIdeal B ^ n)) →
        ∀ (M : Type w) [AddCommGroup M] [Module B M] [Module.Finite B M],
        ∃ Φ : ((B ⊗[(AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime
          q))] (Fin r → (AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)))) →ₗ[B] M) →ₗ[B] ((AdicCompletion (maximalIdeal
          (Localization.AtPrime q)) (Localization.AtPrime q)) → M),
          (∀ t s, Φ t s = t (1 ⊗ₜ[(AdicCompletion (maximalIdeal (Localization.AtPrime q))
            (Localization.AtPrime q))] d s)) ∧
          Function.Injective Φ ∧
          (∀ D : (AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)) →
            M, (∃ t, Φ t = D) ↔
            (D 0 = 0 ∧ (∀ a b, D (a + b) = D a + D b) ∧
              (∀ a : k, D (algebraMap k (AdicCompletion (maximalIdeal (Localization.AtPrime q))
                (Localization.AtPrime q)) a) = 0) ∧
              (∀ a b, D (a * b) =
                (algebraMap (AdicCompletion (maximalIdeal (Localization.AtPrime q))
                  (Localization.AtPrime q)) B a) • D b + (algebraMap (AdicCompletion (maximalIdeal
                  (Localization.AtPrime q)) (Localization.AtPrime q)) B b) • D a) ∧
              (∀ n : ℕ, ∃ N : ℕ, ∀ s ∈ maximalIdeal (AdicCompletion (maximalIdeal
                (Localization.AtPrime q)) (Localization.AtPrime q)) ^ N, D s ∈ (maximalIdeal B ^ n •
                (⊤ : Submodule B M)))))) ∧
      (∀ (E : Type v) [CommRing E] [Algebra k E] [IsLocalRing E]
        [IsNoetherianRing E] [IsAdicComplete (maximalIdeal E) E],
        (∀ g : (AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q))
          →ₐ[k] E, IsLocalHom g → (∀ n : ℕ, ∃ N : ℕ, ∀ s ∈ maximalIdeal (AdicCompletion
          (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)) ^ N, g s ∈ (maximalIdeal
          E ^ n)) →
          IsLocalHom (g.toRingHom.comp (algebraMap (Localization.AtPrime q) (AdicCompletion
            (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q))))) ∧
        (∀ h : (Localization.AtPrime q) →ₐ[k] E, IsLocalHom h →
          ∃! g : (AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q))
            →ₐ[k] E,
            IsLocalHom g ∧ (∀ n : ℕ, ∃ N : ℕ, ∀ s ∈ maximalIdeal (AdicCompletion (maximalIdeal
              (Localization.AtPrime q)) (Localization.AtPrime q)) ^ N, g s ∈ (maximalIdeal E ^ n)) ∧
            ∀ a : (Localization.AtPrime q), g ((algebraMap (Localization.AtPrime q) (AdicCompletion
              (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q))) a) = h a)) ∧
      (∀ (B : Type v) (E : Type w) [CommRing B] [CommRing E]
        [Algebra k B] [Algebra k E] [IsLocalRing B] [IsLocalRing E]
        [IsNoetherianRing B] [IsNoetherianRing E]
        [IsAdicComplete (maximalIdeal B) B] [IsAdicComplete (maximalIdeal E) E]
        (f : (AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)) →ₐ[k]
          B) (π : E →ₐ[k] B),
        IsLocalHom f → (∀ n : ℕ, ∃ N : ℕ, ∀ s ∈ maximalIdeal (AdicCompletion (maximalIdeal
          (Localization.AtPrime q)) (Localization.AtPrime q)) ^ N, f s ∈ (maximalIdeal B ^ n)) →
        IsLocalHom π → Function.Surjective π → RingHom.ker π.toRingHom ^ 2 = ⊥ →
        ∃ g : (AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q))
          →ₐ[k] E,
          IsLocalHom g ∧ (∀ n : ℕ, ∃ N : ℕ, ∀ s ∈ maximalIdeal (AdicCompletion (maximalIdeal
            (Localization.AtPrime q)) (Localization.AtPrime q)) ^ N, g s ∈ (maximalIdeal E ^ n)) ∧
            π.comp g = f) := by
  sorry

end Algebra
