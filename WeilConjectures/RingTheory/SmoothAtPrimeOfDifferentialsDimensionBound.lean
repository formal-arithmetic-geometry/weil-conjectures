/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import WeilConjectures.RingTheory.AlgClosedDifferentialFiberAtClosedPoint
import WeilConjectures.AlgebraicGeometry.SmoothAtMaximalIdeal
import WeilConjectures.RingTheory.ClosedPointDimensionLocalRing
import WeilConjectures.RingTheory.SmoothAtPrimeFieldExtensionDescent

/-!
# A dimension bound on differentials implies smoothness at a prime

A finite type algebra over a field is smooth at a prime if the fibre of its module of
differentials there has dimension at most the topological dimension at that point.

## References

* [Stacks, Tag 00TT], implication (2) implies (1)
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- A finite type algebra over a field is smooth at a prime if the dimension of the fibre
of its module of differentials is at most the topological dimension at that point.
The residue field is placed on the left of the tensor product to give the usual scalar
extension module; exchanging the factors identifies it with the tensor product in 00TT. -/
theorem isSmoothAtPrime_of_finrank_kaehlerDifferential_le
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S] [FiniteType k S]
    (q : PrimeSpectrum S)
    (hdim : (Module.finrank q.asIdeal.ResidueField
      (q.asIdeal.ResidueField ⊗[S] KaehlerDifferential k S) : WithBot ℕ∞) ≤
        topologicalKrullDimAt q) :
    IsSmoothAtPrime k q := by
  obtain ⟨K, hK, hAk, hCK, qK, hmax, hq, hfiber⟩ :=
    exists_algClosed_prime_over_finrank_differentials_eq (k := k) q
  let : Field K := hK
  let : Algebra k K := hAk
  let : IsAlgClosed K := hCK
  let : qK.asIdeal.IsMaximal := hmax
  have hlocal := AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_localizationAtMaximal
    (k := K) (Algebra.FiniteType.iff_quotient_mvPolynomial''.mp inferInstance) qK.asIdeal
  have hdimK : topologicalKrullDimAt q = topologicalKrullDimAt qK := by
    let e := TensorProduct.comm k S K
    let q' := PrimeSpectrum.comap e.toRingEquiv.toRingHom qK
    have hc : PrimeSpectrum.comap
        (TensorProduct.includeLeftRingHom (R := k) (A := S) (B := K)) q' = q := by
      rw [show q' = PrimeSpectrum.comap e.toRingEquiv.toRingHom qK from rfl,
        ← PrimeSpectrum.comap_comp_apply]
      convert hq using 1
      congr 1
    have hd := AlgebraicGeometry.topologicalKrullDimAt_spec_tensorProduct_field_extension q'
    rw [hc] at hd
    let eh := PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv
    have hle : ∀ {X Y : Type (max u v)} [TopologicalSpace X] [TopologicalSpace Y]
        (e : X ≃ₜ Y) (x : X), topologicalKrullDimAt x ≤ topologicalKrullDimAt (e x) := by
      intro X Y _ _ e x
      refine le_iInf₂ fun U hx ↦ ?_
      let V : TopologicalSpace.Opens X := ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩
      let eV : V ≃ₜ U := e.subtype (fun _ ↦ Iff.rfl)
      exact (iInf₂_le V hx).trans_eq
        (IsHomeomorph.topologicalKrullDim_eq eV eV.isHomeomorph)
    have heq : eh.symm qK = q' := by rfl
    have he : topologicalKrullDimAt q' = topologicalKrullDimAt qK := by
      apply le_antisymm
      · have hh := hle eh (eh.symm qK)
        rw [eh.apply_symm_apply, heq] at hh
        exact hh
      · simpa only [heq] using hle eh.symm qK
    exact hd.trans he
  have hbound : (Module.finrank qK.asIdeal.ResidueField
      (qK.asIdeal.ResidueField ⊗[K ⊗[k] S] KaehlerDifferential K (K ⊗[k] S)) :
        WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime qK.asIdeal) := by
    rw [hfiber, ← hlocal, ← hdimK]
    exact hdim
  have hsmooth : IsSmoothAtPrime K qK :=
    smoothAtMaximalIdeal_of_finrank_differentials_le_krullDim K (K ⊗[k] S)
      qK.asIdeal hmax hbound
  exact hq ▸ isSmoothAtPrime_of_fieldExtension qK hsmooth

end Algebra
