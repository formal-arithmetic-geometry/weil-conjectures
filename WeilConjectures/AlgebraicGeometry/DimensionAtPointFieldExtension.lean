/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference
import WeilConjectures.RingTheory.PolynomialPresentationHeightFieldExtension

/-!
# Dimension at a point under extension of the ground field

Source: Stacks Project, Algebra, Lemma 10.116.6, Tag 00P4.
-/

@[expose] public section

universe u v w

open TensorProduct

namespace AlgebraicGeometry

private theorem localDim_homeomorph_le {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    topologicalKrullDimAt x ≤ topologicalKrullDimAt (e x) := by
  refine le_iInf₂ fun U hx ↦ ?_
  let V : TopologicalSpace.Opens X := ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩
  let eV : V ≃ₜ U := e.subtype (fun _ ↦ Iff.rfl)
  exact (iInf₂_le V hx).trans_eq
    (IsHomeomorph.topologicalKrullDim_eq eV eV.isHomeomorph)

private theorem localDim_homeomorph {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (e x) := by
  exact le_antisymm (localDim_homeomorph_le e x)
    (by simpa using localDim_homeomorph_le e.symm (e x))

private theorem localDim_surjective_polynomial
    {k : Type*} [Field k] {S : Type*} [CommRing S] (n : ℕ)
    (f : MvPolynomial (Fin n) k →+* S) (hf : Function.Surjective f)
    (q : PrimeSpectrum S) :
    ∃ h h' : ℕ, q.asIdeal.height = (h : ℕ∞) ∧
      (q.asIdeal.comap f).height = (h' : ℕ∞) ∧ h ≤ h' ∧ h' ≤ n ∧
      topologicalKrullDimAt q = ((n - h' + h : ℕ) : WithBot ℕ∞) := by
  let I := RingHom.ker f
  let e := f.quotientKerEquivOfSurjective hf
  let q' := PrimeSpectrum.comap e.toRingHom q
  obtain ⟨h, h', hh, hh', hle, hle', hd⟩ :=
    topologicalKrullDimAt_polynomial_quotient_eq_height_difference n I q'.asIdeal
  have hq : q'.asIdeal.height = q.asIdeal.height := e.height_comap q.asIdeal
  have hfcomp : e.toRingHom.comp (Ideal.Quotient.mk I) = f := by
    apply RingHom.ext
    intro x
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hf x
  have hq' : q'.asIdeal.comap (Ideal.Quotient.mk I) = q.asIdeal.comap f := by
    rw [show q'.asIdeal = q.asIdeal.comap e.toRingHom from rfl,
      Ideal.comap_comap, hfcomp]
  refine ⟨h, h', hq ▸ hh, hq' ▸ hh', hle, hle', ?_⟩
  have he := localDim_homeomorph (PrimeSpectrum.homeomorphOfRingEquiv e).symm q
  exact he.trans hd

/-- The dimension at a point of the spectrum of a finite type algebra is preserved by any
extension of its ground field. The map `algebraMap k K` is the given field homomorphism;
`S ⊗[k] K` has its right-factor `K`-algebra structure. The displayed prime-spectrum map
contracts the prime along `s ↦ s ⊗ₜ 1` (Stacks, Tag 00P4). -/
theorem topologicalKrullDimAt_spec_tensorProduct_field_extension
    {k : Type u} {K : Type v} {S : Type w} [Field k] [Field K] [CommRing S]
    [Algebra k K] [Algebra k S] [Algebra.FiniteType k S]
    (qK : Spec (.of (S ⊗[k] K))) :
    topologicalKrullDimAt (X := Spec (.of S))
        (PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := S) (B := K)) qK) =
      topologicalKrullDimAt qK := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k S)
  obtain ⟨g, hg, heights⟩ := polynomial_presentation_height_field_extension (K := K) n f hf
  let q := PrimeSpectrum.comap
    (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := S) (B := K)) qK
  obtain ⟨h, h', hh, hh', hle, hn, hd⟩ :=
    localDim_surjective_polynomial n f.toRingHom hf q
  obtain ⟨H, H', hH, hH', hLe, hN, hD⟩ :=
    localDim_surjective_polynomial n g hg qK
  have he := heights qK
  change (q.asIdeal.comap f.toRingHom).height + qK.asIdeal.height =
    (qK.asIdeal.comap g).height + q.asIdeal.height at he
  rw [hh', hH, hH', hh] at he
  have heNat : h' + H = H' + h := by exact_mod_cast he
  have heDim : n - h' + h = n - H' + H := by omega
  exact hd.trans ((congrArg (fun d : ℕ ↦ (d : WithBot ℕ∞)) heDim).trans hD.symm)

end AlgebraicGeometry
