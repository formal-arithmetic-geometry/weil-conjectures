/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.RingTheory.FinitePresentation
import Sheaf.RingTheory.FiniteAlgebraExtremallyDisconnected
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Components of finite finitely presented algebras over w-contractible rings -/

@[expose] public section

universe u

open Topology PrimeSpectrum

private noncomputable def quotientHomeomorphClosedPoints (R : Type u) [CommRing R]
    (I : Ideal R) (hI : zeroLocus I = closedPoints (PrimeSpectrum R)) :
    PrimeSpectrum (R ⧸ I) ≃ₜ closedPoints (PrimeSpectrum R) := by
  refine (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr ?_)
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, hI]

private theorem sepClosedResidueField_of_surjective {R A : Type u}
    [CommRing R] [CommRing A] [IsWStrictlyLocalRing R]
    (g : R →+* A) (hg : Function.Surjective g)
    (p : Ideal A) [p.IsMaximal] : IsSepClosed p.ResidueField := by
  let m := p.comap g
  have : m.IsMaximal := Ideal.comap_isMaximal_of_surjective g hg
  have : IsStrictlyHenselianLocalRing (Localization.AtPrime m) :=
    IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization m
  let φ := (algebraMap A p.ResidueField).comp g
  have hu (s : m.primeCompl) : IsUnit (φ s) := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    apply s.2
    change g s ∈ p
    exact Ideal.algebraMap_residueField_eq_zero.mp h
  let f : Localization.AtPrime m →+* p.ResidueField := IsLocalization.lift hu
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, ha⟩ := p.algebraMap_residueField_surjective x
    obtain ⟨r, rfl⟩ := hg a
    exact ⟨algebraMap R (Localization.AtPrime m) r,
      (IsLocalization.lift_eq hu r).trans ha⟩
  have : IsLocalHom f := hf.isLocalHom
  let ψ := IsLocalRing.ResidueField.lift f
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨r, rfl⟩ := hf x
    exact ⟨IsLocalRing.residue _ r, rfl⟩
  exact IsSepClosed.of_ringEquiv (RingEquiv.ofBijective ψ ⟨ψ.injective, hψ⟩)

private theorem zeroLocus_map_closedPointIdeal (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [IsWLocalRing R] :
    zeroLocus ((vanishingIdeal (closedPoints (PrimeSpectrum R))).map (algebraMap R S)) =
      closedPoints (PrimeSpectrum S) := by
  have hI : zeroLocus (vanishingIdeal (closedPoints (PrimeSpectrum R))) =
      closedPoints (PrimeSpectrum R) := by
    rw [zeroLocus_vanishingIdeal_eq_closure,
      IsClosed.closure_eq WLocalSpace.isClosed_closedPoints]
  ext q
  rw [Ideal.map, zeroLocus_span, ← preimage_comap_zeroLocus, hI]
  simp only [Set.mem_preimage, mem_closedPoints_iff,
    PrimeSpectrum.isClosed_singleton_iff_isMaximal, PrimeSpectrum.comap_asIdeal]
  exact ⟨fun h ↦ Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q.asIdeal h,
    fun h ↦ Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q.asIdeal⟩

/-- The component space of a finite finitely presented algebra over a w-contractible ring
is extremally disconnected.
Source: Stacks Project, Tag 0986, final paragraph, and Tag 0985
(blueprint: lem-ce-finite-finitely-presented-wcontractible-components).

Proof: Let I be the vanishing ideal of the closed points of Spec R. W-locality says that
V(I) is exactly that closed-point locus. The quotient spectrum Spec(R/I) is therefore
homeomorphic to the closed points, hence to the component space of Spec R; it is Hausdorff
and extremally disconnected. Each prime p of R/I is maximal. Its residue field is a
surjective image of the strictly henselian localization R_m at its contraction: invert
elements outside m, which map to units, and use surjectivity of R → R/I → κ(p).
The resulting residue-field isomorphism makes κ(p) separably closed.
Put B = S/IS. The quotient/tensor equivalence identifies it with (R/I) ⊗[R] S, so it is
finite and finitely presented over R/I. Apply the finite-algebra spectrum theorem to get
extremal disconnectedness of Spec B. Integrality gives V(IS) equal to the closed-point
locus of Spec S. Consequently Spec B is homeomorphic to those closed points, and the
assumed w-strict-locality identifies them with the component space of Spec S. Transport
extremal disconnectedness across this homeomorphism. The argument allows empty spectra. -/
theorem extremallyDisconnected_components_of_finite_finitePresentation
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsWContractibleRing R] [Module.Finite R S] [Algebra.FinitePresentation R S]
    [IsWStrictlyLocalRing S] :
    ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum S)) := by
  let I := vanishingIdeal (closedPoints (PrimeSpectrum R))
  let A := R ⧸ I
  let B := S ⧸ I.map (algebraMap R S)
  have hI : zeroLocus I = closedPoints (PrimeSpectrum R) := by
    dsimp only [I]
    rw [zeroLocus_vanishingIdeal_eq_closure,
      IsClosed.closure_eq WLocalSpace.isClosed_closedPoints]
  let hA := quotientHomeomorphClosedPoints R I hI
  have : T2Space (ConnectedComponents (PrimeSpectrum R)) := t2Space_connectedComponent
  have : T2Space (closedPoints (PrimeSpectrum R)) :=
    WLocalSpace.closedPointsHomeomorph.symm.t2Space
  have : T2Space (PrimeSpectrum A) := hA.symm.t2Space
  have : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R)) :=
    IsWContractibleRing.extremallyDisconnected_connectedComponents
  have : ExtremallyDisconnected (PrimeSpectrum A) :=
    extremallyDisconnected_of_homeo (hA.trans WLocalSpace.closedPointsHomeomorph).symm
  have : Module.Finite A B := Module.Finite.equiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toLinearEquiv
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.equiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm
  have hsep (p : PrimeSpectrum A) : IsSepClosed p.asIdeal.ResidueField := by
    have : p.asIdeal.IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp isClosed_singleton
    exact sepClosedResidueField_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective p.asIdeal
  have : ExtremallyDisconnected (PrimeSpectrum B) :=
    extremallyDisconnected_spectrum_of_finite_finitePresentation A B hsep
  let hB := quotientHomeomorphClosedPoints S (I.map (algebraMap R S))
    (zeroLocus_map_closedPointIdeal R S)
  exact extremallyDisconnected_of_homeo (hB.trans WLocalSpace.closedPointsHomeomorph)
