module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Power torsion in the conormal module of a completed retraction

Source: Stacks Project, Tag 0AKJ (lemma-fully-faithful-etale-over-complement),
the existence argument after reduction to A = C, using Tags 0ALQ and 0ALM
(blueprint: lem-per-completed-retraction-conormal-torsion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open AlgebraicGeometry

namespace AdicCompletion

/-- The kernel modulo its square of a completed retraction is killed by a power of `J`.
Source: Stacks Project, Tag 0AKJ (lemma-fully-faithful-etale-over-complement),
existence for A = C (blueprint: lem-per-completed-retraction-conormal-torsion).

An `R`-algebra map between these completions is automatically a map over the completed
base: it is continuous for the extended `J`-adic ideals, and compatibility on the dense
image of `R` extends to its completion. Thus `σ` is exactly a completed-base-algebra
retraction, as in the node. The scalar in the conclusion uses `R → S → Ŝ`.

Proof: (1) Apply lem-per-etale-away-completed-cotangent-torsion to obtain completeness,
finite type reduction and `J^c H⁰(L̂_{Ŝ/R}) = 0`. The base completion is complete and has
reduction `R/J` by lem-weil-pbc-adic-completion-mod-ideal, since `J` is finitely generated.
(2) The structural map `R̂ → Ŝ` is a section of `σ`, so `σ` is surjective. Both maps are
continuous, since an algebra map carries every power of the extended ideal into itself.
(3) Apply lem-per-completed-cotangent-transitivity. The zero-variable presentations of
`R̂` over `R` and over `Ŝ` give respectively the zero complex and `(K/K² → 0)`.
The exact cohomology sequence gives an injection `K/K² → R̂ ⊗[Ŝ] H⁰(L̂_{Ŝ/R})`.
(4) The latter tensor product is annihilated by `J^c`: balancing moves a scalar onto the
second factor, which it kills, and pure tensors generate (def-weil-pbc-module-tensor-product).
Injectivity gives the same annihilation on `K/K²`. Its scalar action is the stipulated
one, since `K` kills `K/K²` and the retraction commutes with scalars. -/
theorem exists_pow_annihilates_completed_retraction_conormal
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    (J : Ideal R) (hfinite : (algebraMap R S).FiniteType)
    (hetale : Etale (morphismRestrict (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (⟨(PrimeSpectrum.zeroLocus (J : Set R))ᶜ,
        (PrimeSpectrum.isClosed_zeroLocus (J : Set R)).isOpen_compl⟩ :
          (Spec (CommRingCat.of R)).Opens)))
    (σ : AdicCompletion (J.map (algebraMap R S)) S →ₐ[R] AdicCompletion J R) :
    ∃ c : ℕ, ∀ (r : R), r ∈ J ^ c → ∀ x : (RingHom.ker σ.toRingHom).Cotangent,
      algebraMap R (AdicCompletion (J.map (algebraMap R S)) S) r • x = 0 := by
  sorry

end AdicCompletion
