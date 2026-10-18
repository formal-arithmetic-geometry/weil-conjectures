/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
public import WeilConjectures.AlgebraicGeometry.UnramifiedOverFieldDiscrete
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomologyPresheaf

/-!
# Higher direct images out of a separably closed point

For a separably closed field `K'` and a morphism `t : Spec K' ⟶ S` to an affine scheme, the
higher direct images `R^q t_* (Λ/dΛ)` vanish for `q ≥ 1`
(`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isSepClosed`): for `U` affine and étale
over `S`, the fibre `U ×_S Spec K'` is a finite disjoint union of copies of `Spec K'`, which has
no higher cohomology. This is the vanishing used at the end of the proof of blueprint
`lem-kun-0f1i-normal`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The residue fields of a scheme étale over a separably closed field `K` are separably
closed: they are finite separable extensions of `K`, hence equal to `K`. -/
theorem Scheme.isSepClosed_residueField_of_etale {K : Type u} [Field K] [IsSepClosed K]
    {Z : Scheme.{u}} (a : Z ⟶ Spec (.of K)) [Etale a] (z : Z) :
    IsSepClosed (Z.residueField z) := by
  have : IsSepClosed ((Spec (.of K)).residueField (a z)) := IsSepClosed.of_ringEquiv
    ((@Ideal.algEquivResidueFieldOfField _ _ _ (PrimeSpectrum.isPrime _)).toRingEquiv.trans
      (Spec.residueFieldIso (.of K) (a z)).commRingCatIsoToRingEquiv.symm)
  let : Algebra ((Spec (.of K)).residueField (a z)) (Z.residueField z) :=
    (a.residueFieldMap z).hom.toAlgebra
  exact IsSepClosed.of_ringEquiv (RingEquiv.ofBijective
    (algebraMap ((Spec (.of K)).residueField (a z)) (Z.residueField z))
    ⟨(a.residueFieldMap z).hom.injective, IsSepClosed.algebraMap_surjective _ _⟩)

/-- A quasi-compact scheme étale over a separably closed field has no étale cohomology in
positive degrees: it is a finite discrete scheme with separably closed residue fields. -/
theorem Etale.subsingleton_H_of_etale_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    {Z : Scheme.{u}} [CompactSpace Z] (a : Z ⟶ Spec (.of K)) [Etale a]
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Subsingleton (Sheaf.H F (n + 1)) := by
  have : DiscreteTopology Z := discreteTopology_of_unramified_over_field a
  have : Finite Z := finite_of_compact_of_discrete
  have : IsEmpty ((⊥ : Z.Opens) : Scheme.{u}) := ⟨fun ⟨y, hy⟩ ↦ by simp at hy⟩
  exact Etale.subsingleton_H_of_isZero_upperStar ⊥ (Set.toFinite _)
    (fun _ _ ↦ isClosed_discrete _) (fun z _ ↦ Scheme.isSepClosed_residueField_of_etale a z) F
    (Scheme.Etale.isZero_sheaf_of_isEmpty _) n

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- For `K'` separably closed and `t : Spec K' ⟶ S` with `S` affine, `R^q t_* (Λ/dΛ) = 0` for
every `q ≥ 1`. -/
theorem Etale.isZero_higherDirectImage_of_isSepClosed {K' : Type u} [Field K'] [IsSepClosed K']
    {S : Scheme.{u}} [IsAffine S] (t : Spec (.of K') ⟶ S) (d : ℕ) {q : ℤ} (hq : 1 ≤ q) :
    IsZero (Etale.higherDirectImage Λ t q (Etale.constantModSheaf Λ (Spec (.of K')) d)) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt (by omega : 0 < n)
  rw [zero_add]
  refine isZero_higherDirectImage_constantModSheaf_of_forall_exists Λ t d (m + 1)
    fun e _ U u _ _ ξ ↦ ⟨PUnit, fun _ ↦ U, fun _ ↦ 𝟙 U, fun _ ↦ inferInstance,
      fun x ↦ ⟨⟨⟩, x, rfl⟩, fun _ ↦ ?_⟩
  have := Etale.subsingleton_H_of_etale_of_isSepClosed (pullback.fst t u)
    ((pullback t u).constantZMod e) m
  rw [Subsingleton.elim ξ 0, map_zero]

end AlgebraicGeometry
