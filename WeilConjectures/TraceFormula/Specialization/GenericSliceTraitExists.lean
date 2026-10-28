/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTrait
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitDVR
public import WeilConjectures.TraceFormula.Specialization.GenericSliceTraitUniversal
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationFunctoriality

/-!

# The strict localization of `𝔸¹_S` is a generic slice trait

The strict henselization `R` of `𝔸¹_S` (`S = Spec k'⟦t⟧`) at the geometric point
`Spec K ⟶ 𝔸¹_S` over the generic point of its special fibre (`AlgebraicGeometry.genericSlicePoint`,
`K = k'(x)^alg`) is a strictly henselian discrete valuation ring, weakly étale over `𝔸¹_S`, and the
generic slice `Spec K⟦t⟧ ⟶ 𝔸¹_S` factors through it by a local injection `R ⟶ K⟦t⟧`
(SGA 4½, [Th. finitude], 3.3). With the geometric generic point `R ⟶ K⟦t⟧ ⟶ Ω_K` and the closed
point `R ⟶ K`, this is a generic slice trait
(`AlgebraicGeometry.genericSliceTraitOfStrictLocalization`,
`AlgebraicGeometry.nonempty_genericSliceTrait`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (k' : Type u) [Field k']

/-- **The strict localization of `𝔸¹_S` at the generic point of its special fibre** as a generic
slice trait: `R` the strict henselization, `Ω' = Ω_K` with `R ⟶ K⟦t⟧ ⟶ Ω_K`, and `κ = K` with the
evaluation `R ⟶ K` at the geometric point. -/
noncomputable def genericSliceTraitOfStrictLocalization : GenericSliceTrait k' where
  R := strictHenselization (genericSlicePoint k')
  isDomain := isDomain_strictHenselization_genericSlicePoint k'
  isDiscreteValuationRing := isDiscreteValuationRing_strictHenselization_genericSlicePoint k'
  Ω := traitGenericField (traitSliceField k')
  κ := traitSliceField k'
  toAffineLine := strictLocalizationToBase (genericSlicePoint k')
  weaklyEtale := weaklyEtale_strictLocalizationToBase_genericSlicePoint k'
  ι := genericSliceRingHom k'
  isLocalHom_ι := inferInstance
  injective_ι :=
    haveI := isDomain_strictHenselization_genericSlicePoint k'
    haveI := isDiscreteValuationRing_strictHenselization_genericSlicePoint k'
    injective_genericSliceRingHom k'
  spec_ι_comp := spec_genericSliceRingHom k'
  a := (algebraMap (PowerSeries (traitSliceField k')) (traitGenericField (traitSliceField k'))).comp
    (genericSliceRingHom k')
  injective_a :=
    haveI := isDomain_strictHenselization_genericSlicePoint k'
    haveI := isDiscreteValuationRing_strictHenselization_genericSlicePoint k'
    (algebraMap_traitGenericField_injective _).comp (injective_genericSliceRingHom k')
  b := (strictHenselizationEval (genericSlicePoint k')).hom
  ker_b := maximalIdeal_strictHenselization.symm
  ωS := traitGenericFieldMap k' (traitSliceField k')
  ωK := RingHom.id _
  ωK_comp_ωS := RingHom.id_comp _
  ωK_comp_a := RingHom.id_comp _
  generic_over := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      reassoc_of% spec_genericSliceRingHom k', traitSlice_over]
    exact traitGenericPoint_traitMap k' (traitSliceField k')
  κS := algebraMap k' (traitSliceField k')
  κK := RingHom.id _
  κK_comp_κS := RingHom.id_comp _
  κK_comp_b := by rw [RingHom.id_comp, constantCoeff_comp_genericSliceRingHom]
  closed_over := by
    rw [CommRingCat.ofHom_hom,
      reassoc_of% spec_map_strictHenselizationEval_comp_strictLocalizationToBase,
      genericSlicePoint, Category.assoc, traitSlice_over]
    exact traitClosedPoint_traitMap k' (traitSliceField k')
  ringChar_κ := (Algebra.ringChar_eq k' (traitSliceField k')).symm

/-- **The strict localization of `𝔸¹_S` at the generic point of its special fibre is a generic
slice trait** (EGA IV₄, 18.8; SGA 4½, [Th. finitude], 3.3). -/
theorem nonempty_genericSliceTrait : Nonempty (GenericSliceTrait k') :=
  ⟨genericSliceTraitOfStrictLocalization k'⟩

end AlgebraicGeometry
