/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Closed-fibre quasi-finiteness under a retraction

Source: Stacks Project, Algebra, Tag 04GG, proof of (8) ⇒ (11), final sentence.
(blueprint: lem-weil-pbc-retraction-base-change-no-quasi-finite)
-/

@[expose] public section

universe u v w x

open scoped TensorProduct

namespace Algebra

private theorem quasiFinite_iff_open_fibre_singleton
    {D : Type*} [CommRing D] {E : Type*} [CommRing E] [Algebra D E]
    [Algebra.FiniteType D E] (q : PrimeSpectrum E) :
    IsQuasiFiniteAtPrime D E q ↔
      IsOpen (Subtype.val ⁻¹' {q} : Set
        (PrimeSpectrum.comap (algebraMap D E) ⁻¹' {q.comap (algebraMap D E)})) := by
  unfold IsQuasiFiniteAtPrime
  rw [← (PrimeSpectrum.preimageHomeomorphFiber D E _).isOpen_preimage]
  apply Iff.of_eq
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  change (PrimeSpectrum.preimageHomeomorphFiber D E _) x =
    (PrimeSpectrum.preimageHomeomorphFiber D E _) ⟨q, rfl⟩ ↔ _
  rw [(PrimeSpectrum.preimageHomeomorphFiber D E _).injective.eq_iff]
  exact Subtype.ext_iff

/-- Source: Stacks Project, Algebra, Tag 04GG, proof of (8) ⇒ (11), the
closed-fibre verification in the final sentence.
(blueprint: lem-weil-pbc-retraction-base-change-no-quasi-finite)

Proof: Give R its R'-algebra structure via τ. Since τ splits the coefficient
map, it is surjective, and so is the tensor coprojection C → R ⊗[R'] C.
Composing this coprojection with e gives a surjection f : C → B, hence an
embedding Spec B → Spec C. Its composite with R' → C is R' →τ R → B.
For a prime q' of C over P, the map C → κ(q') extends to R ⊗[R'] C:
send r in R to the residue of its image under R → R' → C. This map is
R'-linear because a - algebraMap R R' (τ a) lies in ker τ, hence in P,
and therefore maps to zero in κ(q'). Composing with e⁻¹ shows ker f ⊆ q'.
Thus every prime over P lies in the image of the spectrum embedding.
The preimage of this fibre is exactly the fibre over m: contraction along
the surjection τ is injective, and P = τ⁻¹(m). Restricting the embedding
gives a homeomorphism of these fibres. By the prime-fibre homeomorphism
in the definition of IsQuasiFiniteAtPrime, quasi-finiteness is openness of
the singleton in the corresponding fibre subspace. Transport that open
singleton through the restricted homeomorphism and contradict hC.
This argument allows zero rings: the fibre spectra may be empty. -/
theorem no_quasiFiniteAtPrime_of_retraction_baseChange
    {R : Type u} [CommRing R] [IsLocalRing R]
    {R' : Type w} [CommRing R'] [Algebra R R']
    (τ : R' →ₐ[R] R) (P : Ideal R') [P.IsPrime]
    (hP : P = (IsLocalRing.maximalIdeal R).comap τ.toRingHom)
    (C : Type x) [CommRing C] [Algebra R' C] [Algebra.FiniteType R' C]
    (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] :
    letI : Algebra R' R := τ.toRingHom.toAlgebra
    ∀ (_e : (R ⊗[R'] C) ≃ₐ[R] B),
      (∀ q : PrimeSpectrum C, q.asIdeal.LiesOver P → ¬ IsQuasiFiniteAtPrime R' C q) →
      ∀ q : PrimeSpectrum B,
        q.comap (algebraMap R B) = IsLocalRing.maximalIdeal R →
          ¬ IsQuasiFiniteAtPrime R B q := by
  let : Algebra R' R := τ.toRingHom.toAlgebra
  intro e hC
  let f : C →+* B := e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
  have hτ : Function.Surjective τ := by
    intro r
    exact ⟨algebraMap R R' r, τ.commutes r⟩
  have hf : Function.Surjective f := e.surjective.comp
    (Algebra.TensorProduct.includeRight_surjective C hτ)
  have hbase (a : R') :
      f (algebraMap R' C a) = algebraMap R B (τ a) := by
    change e (Algebra.TensorProduct.includeRight (algebraMap R' C a)) = _
    rw [AlgHom.commutes]
    change e (algebraMap R (R ⊗[R'] C) (τ a)) = _
    exact e.commutes _
  let m : PrimeSpectrum R := ⟨IsLocalRing.maximalIdeal R, inferInstance⟩
  let p : PrimeSpectrum R' := ⟨P, inferInstance⟩
  let Z : Set (PrimeSpectrum C) := PrimeSpectrum.comap (algebraMap R' C) ⁻¹' {p}
  have hrange : Z ⊆ Set.range (PrimeSpectrum.comap f) := by
    intro q hq
    have hqP : q.asIdeal.comap (algebraMap R' C) = P := congrArg PrimeSpectrum.asIdeal hq
    let j : R' →+* q.asIdeal.ResidueField :=
      (algebraMap C q.asIdeal.ResidueField).comp (algebraMap R' C)
    let k : R →+* q.asIdeal.ResidueField := j.comp (algebraMap R R')
    have hj (a : R') : j (algebraMap R R' (τ a)) = j a := by
      apply eq_of_sub_eq_zero
      rw [← map_sub]
      change algebraMap C q.asIdeal.ResidueField
        (algebraMap R' C (algebraMap R R' (τ a) - a)) = 0
      apply Ideal.algebraMap_residueField_eq_zero.mpr
      rw [← Ideal.mem_comap, hqP, hP]
      change τ (algebraMap R R' (τ a) - a) ∈ IsLocalRing.maximalIdeal R
      simp
    let gR : R →ₐ[R'] q.asIdeal.ResidueField :=
      { k with commutes' := hj }
    let gT : (R ⊗[R'] C) →ₐ[R'] q.asIdeal.ResidueField :=
      Algebra.TensorProduct.lift gR (IsScalarTower.toAlgHom R' C q.asIdeal.ResidueField)
        (fun _ _ ↦ Commute.all _ _)
    let g : B →+* q.asIdeal.ResidueField := gT.toRingHom.comp e.symm.toRingHom
    have hg : g.comp f = algebraMap C q.asIdeal.ResidueField := by
      ext c
      simp [g, f, gT]
    have hker : RingHom.ker f ≤ q.asIdeal := by
      intro c hc
      apply Ideal.algebraMap_residueField_eq_zero.mp
      rw [← hg]
      change g (f c) = 0
      rw [RingHom.mem_ker.mp hc, map_zero]
    rw [range_comap_of_surjective _ f hf]
    exact hker
  have hcomp : f.comp (algebraMap R' C) = (algebraMap R B).comp τ.toRingHom := by
    ext a
    exact hbase a
  have heq : PrimeSpectrum.comap f ⁻¹' Z =
      PrimeSpectrum.comap (algebraMap R B) ⁻¹' {m} := by
    ext q
    change (q.comap f).comap (algebraMap R' C) = p ↔
      q.comap (algebraMap R B) = m
    rw [← PrimeSpectrum.comap_comp_apply, hcomp, PrimeSpectrum.comap_comp_apply]
    simp only [PrimeSpectrum.ext_iff, PrimeSpectrum.comap_asIdeal]
    change (q.asIdeal.comap (algebraMap R B)).comap τ.toRingHom = P ↔
      q.asIdeal.comap (algebraMap R B) = IsLocalRing.maximalIdeal R
    rw [hP]
    exact (Ideal.comap_injective_of_surjective τ.toRingHom hτ).eq_iff
  let H : (PrimeSpectrum.comap (algebraMap R B) ⁻¹' {m}) ≃ₜ Z :=
    (Homeomorph.setCongr heq.symm).trans
      ((PrimeSpectrum.isEmbedding_comap_of_surjective B f hf).homeomorphOfSubsetRange hrange)
  intro q hq hfin
  have hqm : q.comap (algebraMap R B) = m := PrimeSpectrum.ext hq
  let x : PrimeSpectrum.comap (algebraMap R B) ⁻¹' {m} := ⟨q, hqm⟩
  let y := H x
  have hy : y.val.asIdeal.LiesOver P :=
    ⟨(congrArg PrimeSpectrum.asIdeal y.property).symm⟩
  apply hC y.val hy
  rw [quasiFinite_iff_open_fibre_singleton]
  have hyP : y.val.comap (algebraMap R' C) = p := y.property
  rw [hyP]
  have hxopen := (quasiFinite_iff_open_fibre_singleton q).mp hfin
  rw [hqm] at hxopen
  have hxsingleton : (Subtype.val ⁻¹' {q} : Set
      (PrimeSpectrum.comap (algebraMap R B) ⁻¹' {m})) = {x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, x]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  rw [hxsingleton] at hxopen
  have hyopen : IsOpen ({y} : Set Z) := by
    simpa only [Set.image_singleton] using H.isOpenMap _ hxopen
  have hysingleton : (Subtype.val ⁻¹' {y.val} : Set Z) = {y} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  rwa [hysingleton]

end Algebra
