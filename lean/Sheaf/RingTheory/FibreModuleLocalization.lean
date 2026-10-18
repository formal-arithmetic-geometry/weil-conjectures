import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes

/-!
# Residue-field fibre modules and localization

Source: Stacks Project, Algebra, Tags 00DK, 00DF, and 05BZ
(blueprint: lem-trf-fibre-module-localization).

For a ring map `φ : A →+* B`, a prime `p` of `A` and a `B`-module `N`, the fibre module
`N ⊗_A κ(p)` is identified `B`-linearly with `U⁻¹(N/pN)`, `U = φ(A ∖ p)`, and an element
annihilator equal to a prime `q` over `p` survives the localization. The `B`-module
structure on `N ⊗_A κ(p)` is the one through the left factor (`TensorProduct.leftModule`),
for the `A`-module structure on `N` induced by `φ`. Annihilators are written as
`(⊥ : Submodule B M).colon {z}`, the form used by `RingTheory.annihilatorAssociatedPrimes`
(blueprint: def-weil-pbc-annihilator-associated-primes).
-/


universe u v w

open scoped TensorProduct
open Ideal

namespace RingTheory

set_option autoImplicit false
set_option linter.style.haveILetI false

/-- The tensor product with a residue field is the localization of the prime quotient,
with the annihilator witness preserved.

Source: Stacks Project, Algebra, Lemma Tag 00DK (lemma-tensor-localization), Lemma Tag
00DF (lemma-tensor-product-exact) specialized to a prime quotient, and Lemma Tag 05BZ
(lemma-localize-ass), proof of (2) (blueprint: lem-trf-fibre-module-localization).

Here `A` acts on `N` through `φ` (so `A → B` is the algebra `φ.toAlgebra` and
`A → B → N` is a scalar tower), `pN` is the `B`-span of the `φ a • n` with `a ∈ p`,
`U = φ(A ∖ p)`, and `κ(p)` is `p.ResidueField`, whose elements are the `ā / s̄` with
`s ∉ p`. The first two clauses are the displayed formulas of the isomorphism and of its
inverse; the third is the annihilator clause, in `U⁻¹M` and in the fibre.

Proof (blueprint, step by step):
1. `S = A ∖ p` is multiplicatively closed since `p` is prime, and `U = φ(S)` is a
   submonoid of `B`; `κ(p) = S⁻¹(A/p)` has elements `ā/s̄`. The quotient map
   `N → M = N/pN` is `B`-linear and kills exactly the `φ(r)n`, `r ∈ p`; the quotient-tensor
   lemma (lem-weil-pbc-tensor-over-quotient-ring) identifies `(A/p) ⊗_A N` with `M`.
2. Define `Ψ(n ⊗ ā/s̄) = \overline{φ(a)n}/φ(s)`. It is balanced: changing `n` by `pN`
   changes the numerator by zero, and a witness `t ∈ S` of an equality of fractions in
   `S⁻¹(A/p)` gives the witness `φ(t) ∈ U` in `U⁻¹M`; so `Ψ` descends to the tensor
   product, and it is `B`-linear because `B` acts on the numerator.
3. Define `Θ(n̄/φ(s)) = n ⊗ \overline{1/s}`. Elements `φ(r)n'` with `r ∈ p` go to
   `n' ⊗ \overline{r/s} = 0`, and a witness `φ(t)` of a localization equality is
   cancelled since `t̄` is invertible in `κ(p)`; so `Θ` is well defined. On generators
   `ΘΨ = id` and `ΨΘ = id`, so `Ψ` is a `B`-linear isomorphism with the displayed formulas.
4. Let `q` be prime with `φ⁻¹(q) = p` and `Ann_B(z) = q`. If `b(z/1) = 0`, then
   `φ(s)bz = 0` for some `s ∉ p`, so `φ(s)b ∈ q`; `φ(s) ∉ q` since `s ∉ φ⁻¹(q) = p`, so
   `b ∈ q` by primality. Conversely `bz = 0` gives `b(z/1) = 0`. Hence `Ann_B(z/1) = q`.
5. `Ψ⁻¹` is `B`-linear and bijective, so `Ψ⁻¹(z/1)` has the same annihilator `q`
   (def-weil-pbc-annihilator-associated-primes). -/
theorem fibreModuleLocalization
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] (φ : A →+* B)
    (p : Ideal A) [p.IsPrime] (N : Type w) [AddCommGroup N] [Module B N] :
    letI : Algebra A B := φ.toAlgebra
    letI : Module A N := Module.compHom N φ
    haveI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ∃ e : TensorProduct A N p.ResidueField ≃ₗ[B]
        LocalizedModule (Submonoid.map φ p.primeCompl)
          (N ⧸ Submodule.span B {x : N | ∃ (a : A) (n : N), a ∈ p ∧ x = φ a • n}),
      (∀ (n : N) (a : A) (s : p.primeCompl),
        e (TensorProduct.tmul A n
            (algebraMap A p.ResidueField a * (algebraMap A p.ResidueField s.1)⁻¹)) =
          LocalizedModule.mk
            (Submodule.Quotient.mk (p :=
              Submodule.span B {x : N | ∃ (a : A) (n : N), a ∈ p ∧ x = φ a • n})
              (φ a • n))
            (⟨φ s.1, Submonoid.mem_map_of_mem φ s.property⟩ :
              Submonoid.map φ p.primeCompl)) ∧
      (∀ (n : N) (s : p.primeCompl),
        e.symm (LocalizedModule.mk
            (Submodule.Quotient.mk (p :=
              Submodule.span B {x : N | ∃ (a : A) (n : N), a ∈ p ∧ x = φ a • n}) n)
            (⟨φ s.1, Submonoid.mem_map_of_mem φ s.property⟩ :
              Submonoid.map φ p.primeCompl)) =
          TensorProduct.tmul A n
            (algebraMap A p.ResidueField 1 * (algebraMap A p.ResidueField s.1)⁻¹)) ∧
      (∀ (q : Ideal B), q.IsPrime → q.comap φ = p →
        ∀ z : N ⧸ Submodule.span B {x : N | ∃ (a : A) (n : N), a ∈ p ∧ x = φ a • n},
          (⊥ : Submodule B
              (N ⧸ Submodule.span B {x : N | ∃ (a : A) (n : N), a ∈ p ∧ x = φ a • n})).colon
              {z} = q →
            (⊥ : Submodule B (LocalizedModule (Submonoid.map φ p.primeCompl)
                (N ⧸ Submodule.span B {x : N | ∃ (a : A) (n : N), a ∈ p ∧ x = φ a • n}))).colon
                {LocalizedModule.mk z 1} = q ∧
            (⊥ : Submodule B (TensorProduct A N p.ResidueField)).colon
                {e.symm (LocalizedModule.mk z 1)} = q) := by
  sorry

end RingTheory
