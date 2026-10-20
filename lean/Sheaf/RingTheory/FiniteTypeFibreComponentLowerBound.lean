/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Irreducible
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import WeilConjectures.RingTheory.MinimalComponentDimensionMaximumCore
import WeilConjectures.RingTheory.KrullDimension.FiniteType
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Dimension lower bound for components of a finite-type fibre

Source: Stacks Project, `varieties.tex`, Tag 0B2L, lemma-dimension-fibres-locally-algebraic,
(2)(a) (blueprint: lem-zl-finite-type-fibre-component-lower-bound).

The statement is the affine formulation for a rational closed fibre. The proof combines the
Noetherian height inequality (Stacks, Tag 00OM) with the finite-type dimension formula
(Stacks, Tag 00P1).
-/

@[expose] public section

open Set

universe u v w

namespace Algebra

/-- For a finite-type map of finitely generated algebras over a field, every irreducible
component of a rational closed fibre has dimension at least the dimension of the source
minus the dimension of the image algebra (Stacks, Tag 0B2L (2)(a)).

Proof:
1. Set `P = ker φ`, `A = B/P`, and `J = map φ m`. The kernel is prime because `C`
   is a domain. The finite-type domain dimension theorem gives natural dimensions `dC`
   and `dA` for `C` and `A`.
2. Write the component as `W = V(qbar)` for a minimal prime of `C/J`, and let `q` be
   its inverse image in `C`. Maximality of `m` gives `comap φ q = m`. If `p` is the
   contraction of `q` to `A`, quotient-map identities give `pC = J`.
3. Both `A` and `C` are Noetherian. The height inequality for a prime lying over `p`
   (Stacks, Tag 00OM) gives `height q ≤ height p + height qbar`. Minimality of `qbar`
   makes its height zero, so `height q ≤ height p ≤ dA`.
4. The local-dimension theorem at `q` supplies natural numbers `d` and `r` with
   `height q = d` and `trdeg_k κ(q) = r`. The minimal-component dimension bound,
   applied to the zero prime of the domain `C`, gives `dC ≤ d + r`.
5. The finite-type domain dimension theorem identifies `dim(C/q)` with `r`, since
   its fraction field is `κ(q)`. The third isomorphism theorem and the spectrum-closure
   dimension theorem identify `dim W` with `dim(C/q)`.
6. Now `d ≤ dA` and `dC ≤ d + r` imply `dC - dA ≤ r = dim W`.
The rationality hypothesis is retained in the signature; this argument does not need it.
(blueprint: lem-zl-finite-type-fibre-component-lower-bound)
-/
theorem finiteType_fibre_component_lower_bound
    (k : Type u) [Field k]
    (B : Type v) [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (C : Type w) [CommRing C] [Algebra k C] [Algebra.FiniteType k C] [IsDomain C]
    (φ : B →ₐ[k] C)
    (m : Ideal B) (hm : m.IsMaximal)
    (hmk : Function.Bijective (algebraMap k (B ⧸ m))) :
    ∃ dC dA : ℕ,
      ringKrullDim C = (dC : WithBot ℕ∞) ∧
      ringKrullDim (B ⧸ RingHom.ker φ.toRingHom) = (dA : WithBot ℕ∞) ∧
      ∀ W : Set (PrimeSpectrum (C ⧸ Ideal.map φ.toRingHom m)),
        W ∈ irreducibleComponents (PrimeSpectrum (C ⧸ Ideal.map φ.toRingHom m)) →
          ((dC - dA : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim W := by
  classical
  cases hmk
  -- Use the height inequality at a minimal prime of the closed fibre.
  -- This route does not require the rationality hypothesis.
  let P := RingHom.ker φ.toRingHom
  let A := B ⧸ P
  let π : B →+* A := Ideal.Quotient.mk P
  let ψ : A →ₐ[k] C := Ideal.kerLiftAlg φ
  let : Algebra A C := ψ.toRingHom.toAlgebra
  have : P.IsPrime := RingHom.ker_isPrime φ.toRingHom
  have : IsDomain A := Ideal.Quotient.isDomain P
  obtain ⟨dC, hdC, _, _⟩ := finiteType_domain_ringKrullDim_eq_trdeg (k := k) (S := C)
  obtain ⟨dA, hdA, _, _⟩ := finiteType_domain_ringKrullDim_eq_trdeg (k := k) (S := A)
  refine ⟨dC, dA, hdC, hdA, ?_⟩
  intro W hW
  let J := Ideal.map φ.toRingHom m
  rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hW
  obtain ⟨qbar, hqbar, rfl⟩ := hW
  have : qbar.IsPrime := hqbar.isPrime
  let q := qbar.comap (Ideal.Quotient.mk J)
  have : q.IsPrime := Ideal.comap_isPrime _ qbar
  have hJq : J ≤ q := by
    intro x hx
    change Ideal.Quotient.mk J x ∈ qbar
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact qbar.zero_mem
  have hmq : m ≤ q.comap φ.toRingHom := Ideal.map_le_iff_le_comap.mp hJq
  have hqm : q.comap φ.toRingHom = m :=
    (hm.eq_of_le (Ideal.comap_ne_top φ.toRingHom (inferInstance : q.IsPrime).ne_top) hmq).symm
  let p := q.comap ψ.toRingHom
  have : p.IsPrime := Ideal.comap_isPrime _ q
  have hpπ : p.comap π = m := by
    change q.comap (ψ.toRingHom.comp π) = m
    have hf : ψ.toRingHom.comp π = φ.toRingHom := by ext x; rfl
    rw [hf]
    exact hqm
  have hp : p = m.map π := by
    rw [← hpπ, Ideal.map_comap_of_surjective π Ideal.Quotient.mk_surjective]
  have hmap : p.map (algebraMap A C) = J := by
    change p.map ψ.toRingHom = J
    rw [hp, Ideal.map_map]
    rfl
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have : q.LiesOver p := ⟨rfl⟩
  have hheight := Ideal.height_le_height_add_of_liesOver p q
  have hqmap : q.map (Ideal.Quotient.mk J) = qbar :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective qbar
  rw [hmap, hqmap, Ideal.height_eq_zero_iff.mpr hqbar, add_zero] at hheight
  have hheightA := p.height_le_ringKrullDim_of_isPrime
  rw [hdA] at hheightA
  obtain ⟨d, r, hd, hr, _⟩ :=
    AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_add_trdeg (k := k) q
  have hdheight : q.height = (d : ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q] at hd
    exact WithBot.coe_injective hd
  have hdle : d ≤ dA := by
    have h := hheight.trans (WithBot.coe_le_coe.mp hheightA)
    rw [hdheight] at h
    exact_mod_cast h
  have hsource := AlgebraicGeometry.minimal_component_dimension_maximum_bound
    (k := k) q d r hd hr (⊥ : Ideal C) inferInstance bot_le
    (fun t _ ht ↦ le_bot_iff.mp ht)
  have hsource' : dC ≤ d + r := by
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot C), hdC] at hsource
    exact_mod_cast hsource
  obtain ⟨n, hn, ht, _⟩ :=
    finiteType_domain_ringKrullDim_eq_trdeg (k := k) (S := C ⧸ q)
  have he : Algebra.trdeg k (FractionRing (C ⧸ q)) = Algebra.trdeg k q.ResidueField :=
    ((FractionRing.algEquiv (A := C ⧸ q) q.ResidueField).restrictScalars k).trdeg_eq
  have hnr : n = r := by exact_mod_cast ht.symm.trans (he.trans hr)
  have hdimq : ringKrullDim (C ⧸ q) = (r : WithBot ℕ∞) := by
    simpa [hnr] using hn
  have hdimW : topologicalKrullDim (PrimeSpectrum.zeroLocus (qbar : Set (C ⧸ J))) =
      (r : WithBot ℕ∞) := by
    rw [← PrimeSpectrum.closure_singleton
      (⟨qbar, inferInstance⟩ : PrimeSpectrum (C ⧸ J)),
      PrimeSpectrum.topologicalKrullDim_closure_singleton]
    change ringKrullDim ((C ⧸ J) ⧸ qbar) = (r : WithBot ℕ∞)
    have hdouble := DoubleQuot.quotQuotEquivQuotOfLE hJq
    rw [← hqmap]
    rw [ringKrullDim_eq_of_ringEquiv hdouble]
    exact hdimq
  change ((dC - dA : ℕ) : WithBot ℕ∞) ≤
    topologicalKrullDim (PrimeSpectrum.zeroLocus (qbar : Set (C ⧸ J)))
  rw [hdimW]
  exact_mod_cast (show dC - dA ≤ r by omega)

end Algebra
