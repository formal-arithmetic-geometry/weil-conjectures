/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitSepClosedOfResidue
public import WeilConjectures.TraceFormula.Specialization.SliceTraitResidue
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitExists

/-!

# The fraction field of the strict localization of `𝔸¹_S` is separably closed in `K((t))`

Let `S' = Spec R` be the strict localization of `𝔸¹_S`, `S = Spec k'⟦t⟧`, at the generic point
of its special fibre (`AlgebraicGeometry.genericSliceTraitOfStrictLocalization`), with the
generic slice `ι : R ⟶ K⟦t⟧`, `K = k'(x)^alg`. The residues of `R` in `K` are separable over
`k'(x)` (`AlgebraicGeometry.residue_mem_separableClosure_genericSlicePoint`, from
`AlgebraicGeometry.isSeparable_sliceTraitResidueEval`), so `Frac R` is separably closed in `K((t))`
(`AlgebraicGeometry.genericSliceTraitOfStrictLocalization_mem_range_of_isSeparable`). This is the
field-theoretic input of SGA 4½, [Th. finitude], 3.3–3.4 for the generic slice.

-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

open Scheme

variable (k' : Type u) [Field k']

/-- The map `k'⟦t⟧[x] ⟶ k'(x)`, `f ↦ f(0, x)`. -/
noncomputable def slicePointRatFunc :
    MvPolynomial (ULift.{u} (Fin 1)) (PowerSeries k') →+* RatFunc k' :=
  MvPolynomial.eval₂Hom ((algebraMap k' (RatFunc k')).comp PowerSeries.constantCoeff)
    fun _ ↦ RatFunc.X

lemma algebraMap_comp_slicePointRatFunc :
    (algebraMap (RatFunc k') (traitSliceField k')).comp (slicePointRatFunc k') =
      sliceTraitPointRingHom (PowerSeries.constantCoeff (R := k')) := by
  ext
  · simp only [slicePointRatFunc, sliceTraitPointRingHom, RingHom.coe_comp, Function.comp_apply,
      MvPolynomial.eval₂Hom_C]
    exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
  · simp [slicePointRatFunc, sliceTraitPointRingHom, traitSliceCoord]

/-- The map `κ(𝔮) ⟶ k'(x)` from the residue field of `k'⟦t⟧[x]` at the prime of the generic
point of the special fibre. -/
noncomputable def slicePrimeRatFunc :
    (RingHom.ker (sliceTraitPointRingHom (PowerSeries.constantCoeff (R := k')))).ResidueField →+*
      RatFunc k' :=
  Ideal.ResidueField.lift _ (slicePointRatFunc k')
    (fun a ha ↦ by
      rw [RingHom.mem_ker] at ha ⊢
      apply (algebraMap (RatFunc k') (traitSliceField k')).injective
      rw [map_zero, ← RingHom.comp_apply, algebraMap_comp_slicePointRatFunc, ha])
    (fun a ha ↦ by
      simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
      intro h
      apply ha
      rw [SetLike.mem_coe, RingHom.mem_ker, ← algebraMap_comp_slicePointRatFunc,
        RingHom.comp_apply, h, map_zero])

lemma algebraMap_comp_slicePrimeRatFunc :
    (algebraMap (RatFunc k') (traitSliceField k')).comp (slicePrimeRatFunc k') =
      slicePrimeResidueFieldHom (PowerSeries.constantCoeff (R := k')) := by
  apply Ideal.ResidueField.ringHom_ext
  refine RingHom.ext fun r ↦ ?_
  simp only [RingHom.coe_comp, Function.comp_apply, slicePrimeRatFunc,
    Ideal.ResidueField.lift_algebraMap, slicePrimeResidueFieldHom_algebraMap]
  rw [← RingHom.comp_apply, algebraMap_comp_slicePointRatFunc]

/-- **The residues of the strict localization at the slice point are separable over `k'(x)`.** -/
theorem residue_mem_separableClosure_sliceTraitPoint
    (r : strictHenselization (sliceTraitPoint (PowerSeries.constantCoeff (R := k')))) :
    (strictHenselizationEval (sliceTraitPoint (PowerSeries.constantCoeff (R := k')))).hom r ∈
      separableClosure (RatFunc k') (traitSliceField k') := by
  have h := isSeparable_sliceTraitResidueEval (PowerSeries.constantCoeff (R := k')) (residue _ r)
  have h₂ := isSeparable_of_comp_eq _ (slicePrimeRatFunc k')
    (algebraMap (RatFunc k') (traitSliceField k')) (RingHom.id _)
    (by rw [RingHom.id_comp]; exact algebraMap_comp_slicePrimeRatFunc k') _ h
  rw [sliceTraitResidueEval, ResidueField.lift_residue_apply, RingHom.id_apply] at h₂
  rw [mem_separableClosure_iff]
  convert h₂
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

/-- The residues of the strict localization of `𝔸¹_S` at the generic point of its special fibre
are separable over `k'(x)`. -/
theorem residue_mem_separableClosure_genericSlicePoint
    (r : strictHenselization (genericSlicePoint k')) :
    (strictHenselizationEval (genericSlicePoint k')).hom r ∈
      separableClosure (RatFunc k') (traitSliceField k') := by
  have key : ∀ (s) (hs : s = sliceTraitPoint (PowerSeries.constantCoeff (R := k')))
      (r : strictHenselization s), (strictHenselizationEval s).hom r ∈
        separableClosure (RatFunc k') (traitSliceField k') := by
    intro s hs r
    subst hs
    exact residue_mem_separableClosure_sliceTraitPoint k' r
  exact key _ (genericSlicePoint_eq_sliceTraitPoint k') r

/-- **`Frac S'` is separably closed in `K((t))`** for the strict localization `S'` of `𝔸¹_S` at
the generic point of its special fibre: every element of `K((t))` separable over `Frac S'` lies
in `Frac S'` (SGA 4½, [Th. finitude], 3.3–3.4). -/
theorem genericSliceTraitOfStrictLocalization_mem_range_of_isSeparable [IsSepClosed k']
    (y : FractionRing (PowerSeries (traitSliceField k')))
    (hy : letI := (IsDiscreteValuationRing.fractionRingLift
        (genericSliceTraitOfStrictLocalization k').ι
        (genericSliceTraitOfStrictLocalization k').injective_ι).toAlgebra
      IsSeparable (FractionRing (genericSliceTraitOfStrictLocalization k').R) y) :
    y ∈ (IsDiscreteValuationRing.fractionRingLift (genericSliceTraitOfStrictLocalization k').ι
      (genericSliceTraitOfStrictLocalization k').injective_ι).range :=
  (genericSliceTraitOfStrictLocalization k').mem_range_of_isSeparable (fun r ↦ by
    change (PowerSeries.constantCoeff.comp (genericSliceRingHom k')) r ∈ _
    rw [constantCoeff_comp_genericSliceRingHom]
    exact residue_mem_separableClosure_genericSlicePoint k' r) y hy

end AlgebraicGeometry
