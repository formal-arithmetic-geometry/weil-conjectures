/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.KunnethCoefficientChangeResidueIff
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.SplitMonoReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseHypotheses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceIntegralSplit
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceTorsion
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethClosure
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethSplitMono

/-!

# The generic-slicing step of Gabber's Künneth formula with `𝒪_E`-coefficients

Let `P` be the product over `S = Spec k'⟦t⟧` of models `M`, `N` of finite type, `b` a coordinate
of `M` and `A₀`, `B₀` bounded constructible `𝒪_E`-complexes. If the Künneth map `Π''` of the
geometric slice over `Spec K⟦t⟧` is invertible, so is the pullback `x₀ = Lσ_s^* Π_{A₀,B₀}` of the
Künneth map to the special fibre of the slice of `P`
(`NearbyCyclesModel.isIso_map_kunnethMap_of_isIso_sliceFst_padicIntegers`). In the square
```
x₀ ≫ a = δ ≫ (u_M ⊗ u_N) ≫ Π''
```
of `NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`, `u_N` is invertible (Th. finitude 3.7,
`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap_padicIntegers`) and `u_M` is a
split monomorphism
(`NearbyCyclesModel.isSplitMono_pullbackExchange_baseChangeHom_traitSlice_padicIntegers`), so
`x₀` is a split monomorphism (`NearbyCyclesModel.isSplitMono_map_kunnethMap_of_isSplitMono`). Its
target is derived complete, being the pullback of the nearby cycles of a bounded constructible
complex, and its reduction modulo `ϖ` is invertible by the generic-slicing step with
`𝔽_E`-coefficients
(`NearbyCyclesModel.isIso_map_kunnethMap_of_isIso_sliceFst_residueField`), so `x₀` is invertible
(`ProEtale.CondensedRing.isIso_of_isSplitMono_of_isIso_extendScalars_map`). The source of `x₀`,
a tensor product of derived complete complexes, need not be derived complete: this is why the
splitting is needed.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {k' : Type u}
  [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}

set_option hygiene false in
/-- The condensed ring `𝒪̲_E`. -/
local notation "𝒪" => Profinite.padicIntegersRingObj ℓ E.1

set_option maxHeartbeats 1600000 in
set_option profiler true in
-- the square of the Künneth maps of the slice is a large term
/-- **The generic-slicing step with `𝒪_E`-coefficients** (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Finite support"; Illusie, *Autour du théorème de
monodromie locale*, proof of Thm. 4.7): for the product `P` over the strictly henselian trait
`S = Spec k'⟦t⟧` of models `M`, `N` of finite type, a coordinate `b` of `M` and bounded
constructible `𝒪_E`-complexes `A₀`, `B₀`, if the Künneth map of the geometric slice
(`NearbyCyclesModel.sliceFst`, `NearbyCyclesModel.sliceSnd`) is invertible, so is the pullback
of `Π_{A₀,B₀}` to the special fibre of the slice of `P`. -/
theorem isIso_map_kunnethMap_of_isIso_sliceFst_padicIntegers [TopologicalSpace.NoetherianSpace Z]
    (hM : M.IsTraitModelOver qM gM)
    (hN : N.IsTraitModelOver qN gN) (hpb : IsPullback φ₁.total φ₂.total qM qN)
    (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
    (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
    (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qM)
    {A₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj 𝒪 X))} (hA₀ : boundedConstructible (condensedRingObj 𝒪 X) A₀)
    {B₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj 𝒪 Y))} (hB₀ : boundedConstructible (condensedRingObj 𝒪 Y) B₀)
    (h : IsIso (kunnethMap 𝒪 (sliceFst hM hP hb) (sliceSnd hN hpb hP hgen hb) A₀ B₀)) :
    IsIso (L((baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
        (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))^*⟦𝒪⟧).map
      (kunnethMap 𝒪 φ₁ φ₂ A₀ B₀)) := by
  -- bounds below of `A₀`, `B₀` and of their external product
  obtain ⟨a, ha⟩ := hA₀.1.1
  obtain ⟨a', ha'⟩ := hB₀.1.1
  have : A₀.IsGE (min a a') := DerivedCategory.TStructure.t.isGE_of_ge A₀ _ _ (min_le_left a a')
  have : B₀.IsGE (min a a') :=
    DerivedCategory.TStructure.t.isGE_of_ge B₀ _ _ (min_le_right a a')
  have hAB : boundedConstructible (condensedRingObj 𝒪 Z)
      (L((f₁)^*⟦𝒪⟧).obj A₀ ⊗ L((f₂)^*⟦𝒪⟧).obj B₀) :=
    boundedConstructible_tensorObj
      (PadicIntegersRingObj.lisseHypotheses ℓ E.1).toLisseTensorHypotheses
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f₁ A₀ hA₀)
      (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f₂ B₀ hB₀)
  obtain ⟨c, hc⟩ := hAB.1.1
  -- the exchange of the change of trait of `N` is invertible, that of the slice of `M` splits
  have hu₂ := isIso_pullbackExchange_baseChangeHom_traitMap_padicIntegers (K := traitSliceField k')
    hN E (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ N.ε B₀ hB₀)
  have hu₁ := isSplitMono_pullbackExchange_baseChangeHom_traitSlice_padicIntegers hM b hb E
    (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ M.ε A₀ hA₀)
  have hπ : IsIso (kunnethMap 𝒪 (sliceFst hM hP hb) (sliceSnd hN hpb hP hgen hb)
      (L((𝟙 X)^*⟦𝒪⟧).obj A₀) (L((𝟙 Y)^*⟦𝒪⟧).obj B₀)) :=
    isIso_kunnethMap_of_iso _ _ _ ((leftDerivedUpperStarId _ X).app A₀)
      ((leftDerivedUpperStarId _ Y).app B₀) h
  -- the pullback of the Künneth map is a split monomorphism
  have hx : IsSplitMono (L((baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
        (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))^*⟦𝒪⟧).map
      (kunnethMap 𝒪 φ₁ φ₂ A₀ B₀)) := by
    refine isSplitMono_map_kunnethMap_of_isSplitMono 𝒪 φ₁ φ₂
      (sliceFst hM hP hb) (sliceSnd hN hpb hP hgen hb)
      (baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over (traitSliceCoord k')))
      (baseChangeHom hN qN (Category.comp_id qN) (traitMap k' (traitSliceField k'))
        (Category.comp_id _))
      (baseChangeHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb) (traitSlice (traitSliceCoord k'))
        (traitSlice_over (traitSliceCoord k'))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ A₀ B₀ ?_ ?_ ?_
    rotate_left 8
    · exact_mod_proofs hu₁
    · exact_mod_proofs hu₂
    · exact_mod_proofs hπ
    · exact Hom.baseChange_total_comp hM hP _ _ _ _ φ₁ _ _ _ rfl
    · exact Hom.baseChange_generic_comp hM hP _ _ _ _ φ₁ _ _ _ rfl
    · exact Hom.baseChange_total_comp hN hP _ _ _ _ φ₂ _ _ _ hgen.symm
    · exact Hom.baseChange_generic_comp hN hP _ _ _ _ φ₂ _ _ _ hgen.symm
    · simp
    · exact Hom.baseChangeSpecial_comp hM hP _ _ _ _ φ₁ _ _ _
    · simp
    · exact Hom.baseChangeSpecial_comp hN hP _ _ _ _ φ₂ _ _ _
  -- finiteness properties of the total spaces and of the special and generic fibres
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hN.locallyOfFiniteType
  have := hN.quasiCompact
  have := hP.locallyOfFiniteType
  have := hP.quasiCompact
  have := hP.isSeparated
  have : LocallyOfFiniteType gM := MorphismProperty.of_isPullback hM.isPullback_j ‹_›
  have : LocallyOfFiniteType gN := MorphismProperty.of_isPullback hN.isPullback_j ‹_›
  have : QuasiCompact gM := MorphismProperty.of_isPullback hM.isPullback_j ‹_›
  have : QuasiCompact gN := MorphismProperty.of_isPullback hN.isPullback_j ‹_›
  have := QuasiCompact.compactSpace_of_compactSpace gM
  have := QuasiCompact.compactSpace_of_compactSpace gN
  have : IsNoetherian M.generic := isNoetherian_of_locallyOfFiniteType gM
  have : IsNoetherian N.generic := isNoetherian_of_locallyOfFiniteType gN
  have : QuasiCompact (φ₁.generic ≫ gM) := MorphismProperty.of_isPullback hP.isPullback_j ‹_›
  have : QuasiSeparated (φ₁.generic ≫ gM) :=
    MorphismProperty.of_isPullback hP.isPullback_j inferInstance
  have : LocallyOfFiniteType (φ₁.generic ≫ gM) :=
    MorphismProperty.of_isPullback hP.isPullback_j ‹_›
  have := QuasiCompact.compactSpace_of_compactSpace (φ₁.generic ≫ gM)
  have := quasiSeparatedSpace_of_quasiSeparated (φ₁.generic ≫ gM)
  have : IsNoetherian P.generic := isNoetherian_of_locallyOfFiniteType (φ₁.generic ≫ gM)
  have : QuasiCompact P.i := MorphismProperty.of_isPullback hP.isPullback_i.flip inferInstance
  have : QuasiSeparated P.i := MorphismProperty.of_isPullback hP.isPullback_i.flip inferInstance
  have := QuasiCompact.compactSpace_of_compactSpace (φ₁.total ≫ qM)
  have := quasiSeparatedSpace_of_quasiSeparated (φ₁.total ≫ qM)
  have := QuasiCompact.compactSpace_of_compactSpace P.i
  have := quasiSeparatedSpace_of_quasiSeparated P.i
  have : IsAffine 𝔸(ULift.{u} (Fin 1); trait k') :=
    inferInstanceAs (IsAffine 𝔸(ULift.{u} (Fin 1); trait k'))
  have : QuasiCompact (traitSlice (k' := k') (traitSliceCoord k')) := inferInstance
  have : QuasiSeparated (traitSlice (k' := k') (traitSliceCoord k')) := inferInstance
  have : QuasiCompact (traitClosedPoint.{u} (traitSliceField k')) := inferInstance
  have : QuasiSeparated (traitClosedPoint.{u} (traitSliceField k')) := inferInstance
  have : CompactSpace (baseChangeSpecial (φ₁.total ≫ b) (traitSlice (traitSliceCoord k'))).left :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.fst (pullback.snd (φ₁.total ≫ b) (traitSlice (traitSliceCoord k')))
        (traitClosedPoint (traitSliceField k')) ≫
          pullback.fst (φ₁.total ≫ b) (traitSlice (traitSliceCoord k')))
  have : QuasiSeparatedSpace
      (baseChangeSpecial (φ₁.total ≫ b) (traitSlice (traitSliceCoord k'))).left :=
    quasiSeparatedSpace_of_quasiSeparated
      (pullback.fst (pullback.snd (φ₁.total ≫ b) (traitSlice (traitSliceCoord k')))
        (traitClosedPoint (traitSliceField k')) ≫
          pullback.fst (φ₁.total ≫ b) (traitSlice (traitSliceCoord k')))
  -- the target of `x₀` is derived complete
  have hV := derivedCompleteIntegers_leftDerivedUpperStar_obj
    (baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
      (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))
    (derivedCompleteIntegers_leftDerivedUpperStar_obj P.i
      (derivedCompleteIntegers_rightDerivedLowerStar_obj P.j
        (derivedCompleteIntegers_of_boundedConstructible
          (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ P.ε _ hAB))))
  -- the reduction of `x₀` modulo `ϖ` is the generic-slicing step with `𝔽_E`-coefficients
  have : (L((f₁)^*⟦𝒪⟧).obj A₀ ⊗ L((f₂)^*⟦𝒪⟧).obj B₀).IsGE c := hc
  have hred := (isIso_map_map_kunnethMap_iff_residueField ℓ E φ₁ φ₂
    (baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
      (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k'))) A₀ B₀
    (min a a') c).2 (isIso_map_kunnethMap_of_isIso_sliceFst_residueField E hM hN hpb hP hgen hb
      ((boundedConstructible _).prop_of_iso ((derivedUpperStarExtendScalarsIso
        (Profinite.padicIntegersRingObjToResidueField ℓ E.1) M.ε).app A₀)
        (boundedConstructible_derivedExtendScalars_residueField M.generic ℓ E.1 _
          (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ M.ε A₀ hA₀)))
      ((boundedConstructible _).prop_of_iso ((derivedUpperStarExtendScalarsIso
        (Profinite.padicIntegersRingObjToResidueField ℓ E.1) N.ε).app B₀)
        (boundedConstructible_derivedExtendScalars_residueField N.generic ℓ E.1 _
          (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ N.ε B₀ hB₀)))
      ((isIso_map_kunnethMap_iff_residueField ℓ E (sliceFst hM hP hb)
        (sliceSnd hN hpb hP hgen hb) A₀ B₀ (min a a') c).1 (Functor.map_isIso _ _)))
  exact isIso_of_isSplitMono_of_isIso_extendScalars_map E _ hV hred

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
