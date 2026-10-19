/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.RingTheory.QuasiFiniteAtPrime

/-!
# Quasi-finiteness at a prime over an intermediate ring

Source: Stacks Project, Algebra, Lemma 10.122.10 (Tag 0C6H)
(blueprint: lem-weil-pbc-quasi-finite-at-prime-permanence).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- (blueprint: lem-weil-pbc-quasi-finite-at-prime-permanence) If `A → B → C` is a
commutative ring tower, `C` is of finite type over `A`, and `A → C` is quasi-finite at
`r`, then `B → C` is quasi-finite at `r` (Stacks Project, Algebra, Tag 0C6H).

Proof: Finite algebra generators over `A` also generate over `B`, by Mathlib's
`FiniteType.of_restrictScalars_finiteType`. Put `p = r ∩ A` and `q = r ∩ B`.
Mathlib's `PrimeSpectrum.preimageHomeomorphFiber` identifies each fibre-ring spectrum
with the corresponding fibre subspace of `Spec C` (Stacks, Tag 00E6). Transport the
open singleton supplied by the hypothesis to the fibre over `p`. The scalar-tower
identity shows that the fibre over `q` includes into the fibre over `p`; this inclusion
is continuous because both fibres carry the subspace topology from `Spec C`.
Its inverse image of the singleton at `r` is precisely the singleton at `r`.
Pull back openness, then transport it through the fibre homeomorphism over `B`.
This proves the required isolated-point condition, following the subset argument of
Tag 0C6H without constructing a comparison homomorphism of fibre rings. -/
theorem IsQuasiFiniteAtPrime.of_restrictScalars
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [FiniteType A C] (r : PrimeSpectrum C) (hr : IsQuasiFiniteAtPrime A C r) :
    @IsQuasiFiniteAtPrime B C _ _ _
      (FiniteType.of_restrictScalars_finiteType A B C) r := by
  have : FiniteType B C := FiniteType.of_restrictScalars_finiteType A B C
  let p := r.comap (algebraMap A C)
  let q := r.comap (algebraMap B C)
  let eA := PrimeSpectrum.preimageHomeomorphFiber A C p
  let eB := PrimeSpectrum.preimageHomeomorphFiber B C q
  let i : (PrimeSpectrum.comap (algebraMap B C) ⁻¹' {q}) →
      (PrimeSpectrum.comap (algebraMap A C) ⁻¹' {p}) := fun x =>
    ⟨x.1, by
      change x.1.comap (algebraMap A C) = r.comap (algebraMap A C)
      rw [IsScalarTower.algebraMap_eq A B C, PrimeSpectrum.comap_comp_apply,
        PrimeSpectrum.comap_comp_apply]
      exact congrArg (PrimeSpectrum.comap (algebraMap A B)) x.2⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  have hA : IsOpen ({⟨r, rfl⟩} : Set (PrimeSpectrum.comap (algebraMap A C) ⁻¹' {p})) := by
    change IsOpen ({eA ⟨r, rfl⟩} : Set (PrimeSpectrum (p.asIdeal.Fiber C))) at hr
    convert hr.preimage eA.continuous using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, eA.injective.eq_iff]
  have hB : IsOpen ({⟨r, rfl⟩} : Set (PrimeSpectrum.comap (algebraMap B C) ⁻¹' {q})) := by
    have h := hA.preimage hi
    convert h using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl
      rfl
    · intro hx
      apply Subtype.ext
      exact congrArg (fun y : (PrimeSpectrum.comap (algebraMap A C) ⁻¹' {p}) => y.1) hx
  change IsOpen ({eB ⟨r, rfl⟩} : Set (PrimeSpectrum (q.asIdeal.Fiber C)))
  simpa only [Set.image_singleton] using eB.isOpenMap _ hB

end Algebra
