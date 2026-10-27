module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.RingTheory.CompleteDVRFiniteNormalization
import WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Basic

/-! # Epp's purely inseparable degree-p alternative

Source: Stacks Project, More on Algebra, Tag 09EY, lemma-purely-inseparable-case,
specialized to complete DVRs (blueprint: lem-sfb-epp-purely-inseparable-degree-p).
-/

@[expose] public section

set_option autoImplicit false

universe uA uB uC uK uL uM

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- The three alternatives for a purely inseparable extension of degree p.
The subalgebras in the third alternative are required to equal the actual integral
closures. The two maps are fixed by their ambient inclusions: the first is induced by
k ↦ 1 ⊗ k and the second by l ⊗ k ↦ l ⊗ k along L → M, followed by reduction.
Thus these are the canonical normalization maps, not freely chosen homomorphisms.

Source: Stacks Project, More on Algebra, Tag 09EY, complete-DVR specialization
(blueprint: lem-sfb-epp-purely-inseparable-degree-p).

Proof:
1. By lem-per-complete-dvr-finite-normalization, C is the normalization of B in M.
   Use lem-weil-pbc-dvr-unit-times-uniformizer-power to write t = v z^e in C.
   If e = 1, alternative (i) holds. Otherwise z^p lies in L, and restriction of
   valuations gives p = e v_B(z^p), hence e = p. Write z^p = ut, with u a unit
   in B. Distinct valuations modulo p make 1,z,...,z^(p-1) a basis of M/L.
2. By lem-sbc-dvr-uniformizer-root-algebra and complete finite normalization,
   D = B[s]/(s^p-t) is the complete normalization in L[s]. Apply
   lem-sfb-epp-frobenius-uniformizer-digits: either u has a pth root w in D,
   or u = sum_{i<m} b_i^p t^i + b t^m with non-pth-power residue of b.
3. In the root case, z ↦ ws identifies M with L[s], and normalization identifies
   C with D. Transporting s back gives alternative (ii) as equality inside M.
4. In the finite-expansion case set n = m+2. By
   lem-sfb-epp-separable-uniformizer-approximation choose a separable, totally
   ramified degree-p extension with t = s^p + s^(np)a. By
   lem-sfb-epp-totally-ramified-base-change, L₁ is a field and B₁ is a complete
   DVR with uniformizer s, residue field k_B, and m_A₁ B₁ = m_B₁.
5. Put h = 1+s^((n-1)p)a and Q = sum_{i<m} b_i s^(i+1). Expanding in
   characteristic p gives ut-Q^p = b s^((m+1)p) + s^(np)d. Hence this equals
   s^((m+1)p)c, where c = b+s^((n-m-1)p)d has the same residue as b.
6. By lem-sfb-epp-residue-nonpower-root-dvr, L₁[Y]/(Y^p-c) is a degree-p
   field and its normalization T over B₁ is a DVR with uniformizer s.
   The change Z = Q+s^(m+1)Y identifies it with M ⊗_K K₁; reduction changes
   neither field. Complete finite normalization gives completeness of T.
7. Every element of C is integral over B, so C maps into T. Conversely an
   element integral over C is integral over T and lies in T by normality
   (lem-weil-pbc-pid-noetherian-normal). T is finite over B₁ and B₁ over B;
   the same finite generators span T over C, so T is integral over C by
   lem-weil-pbc-finite-algebra-is-integral. Thus C₁ = T. Its uniformizer s
   gives m_B₁ C₁ = m_C₁, proving alternative (iii).
-/
theorem epp_purelyInseparable_degree_prime
    (p : ℕ) (hp : p.Prime)
    (A : Type uA) (B : Type uB) (C : Type uC)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
    (hAB : Function.Injective (algebraMap A B))
    (hBC : Function.Injective (algebraMap B C))
    (K : Type uK) (L : Type uL) (M : Type uM)
    [Field K] [Field L] [Field M]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra C M] [IsFractionRing C M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [Algebra B M] [IsScalarTower B L M] [IsScalarTower B C M]
    [Algebra A M] [IsScalarTower A K M] [IsScalarTower A C M]
    [Module.Finite L M] [IsPurelyInseparable L M]
    (hdegree : Module.finrank L M = p)
    (hweak : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal B)
    [CharP (IsLocalRing.ResidueField A) p]
    (t : A) (ht : Irreducible t) :
    Ideal.map (algebraMap A C) (IsLocalRing.maximalIdeal A) =
        IsLocalRing.maximalIdeal C ∨
    (∃ s : M, s ^ p = algebraMap A M t ∧
      (algebraMap C M).range = Subring.closure ((algebraMap B M).range ∪ {s})) ∨
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁)
      (_ : Algebra A K₁) (_ : IsScalarTower A K K₁),
      Module.Finite K K₁ ∧ Algebra.IsSeparable K K₁ ∧ Module.finrank K K₁ = p ∧
      IsField ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ∧
      IsField ((M ⊗[K] K₁) ⧸ nilradical (M ⊗[K] K₁)) ∧
      ∃ (A₁ : Subalgebra A K₁)
        (B₁ : Subalgebra B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
        (C₁ : Subalgebra C ((M ⊗[K] K₁) ⧸ nilradical (M ⊗[K] K₁))),
        A₁ = integralClosure A K₁ ∧
        B₁ = integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ∧
        C₁ = integralClosure C ((M ⊗[K] K₁) ⧸ nilradical (M ⊗[K] K₁)) ∧
        ∃ (_ : IsDomain B₁) (_ : IsDomain C₁)
          (_ : IsDiscreteValuationRing A₁) (_ : IsDiscreteValuationRing B₁)
          (_ : IsDiscreteValuationRing C₁) (_ : IsLocalHom (algebraMap A A₁)),
          IsAdicComplete (IsLocalRing.maximalIdeal A₁) A₁ ∧
          IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁ ∧
          IsAdicComplete (IsLocalRing.maximalIdeal C₁) C₁ ∧
          ∃ (f : A₁ →+* B₁) (g : B₁ →+* C₁),
            (∀ a : A₁, (f a : (L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) =
              Ideal.Quotient.mk (nilradical (L ⊗[K] K₁)) (1 ⊗ₜ[K] (a : K₁))) ∧
            (∀ b : B₁, (g b : (M ⊗[K] K₁) ⧸ nilradical (M ⊗[K] K₁)) =
              Ideal.quotientMap (nilradical (M ⊗[K] K₁))
                (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
                  (AlgHom.id K K₁)).toRingHom
                (fun x hx ↦ mem_nilradical.mpr ((mem_nilradical.mp hx).map
                  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K L M)
                    (AlgHom.id K K₁)).toRingHom))
                (b : (L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))) ∧
            IsLocalHom f ∧ IsLocalHom g ∧
            Function.Injective f ∧ Function.Injective g ∧
            Function.Surjective
              (IsLocalRing.ResidueField.map (algebraMap A A₁)) ∧
            Ideal.map (algebraMap A A₁) (IsLocalRing.maximalIdeal A) =
              IsLocalRing.maximalIdeal A₁ ^ Module.finrank K K₁ ∧
            Ideal.map f (IsLocalRing.maximalIdeal A₁) = IsLocalRing.maximalIdeal B₁ ∧
            Ideal.map g (IsLocalRing.maximalIdeal B₁) = IsLocalRing.maximalIdeal C₁ := by
  sorry

end IsDiscreteValuationRing
