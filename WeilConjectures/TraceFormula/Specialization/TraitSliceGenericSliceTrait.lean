/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTrait
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeFiniteCoefficient
public import WeilConjectures.Tactic.TransportExact
public import WeilConjectures.TraceFormula.Specialization.TraitModelRestrict
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGeneric
public import WeilConjectures.Tactic.ExactModProofs

/-!

# The slice over `Spec K⟦t⟧` as a change of trait of the slice over a generic slice trait

Let `M` be a model over the trait `S = Spec k'⟦t⟧` with a coordinate `b : 𝒳 ⟶ 𝔸¹_S`, and let
`D` be a generic slice trait of `𝔸¹_S` (`AlgebraicGeometry.GenericSliceTrait`), the strict
localization `S' = Spec R` of `𝔸¹_S` at the generic point of its special fibre, through which the
generic slice `σ : T = Spec K⟦t⟧ ⟶ 𝔸¹_S` factors by `D.ι : R ⟶ K⟦t⟧`. The geometric slice
`M'' = M ×_{𝔸¹_S} T` (`NearbyCyclesModel.baseChange`) is then the base change of the slice
`M' = M ×_{𝔸¹_S} S'` (`NearbyCyclesModel.sliceTraitModel`) along the change of strictly
henselian traits `T ⟶ S'`:
```
𝒳'' = 𝒳 ×_{𝔸¹_S} T ──τ──→ 𝒳' = 𝒳 ×_{𝔸¹_S} S'
        │                        │
        T ──────── D.ι ────────→ S'
```
is cartesian (`NearbyCyclesModel.isPullback_genericSliceTraitChangeTotal'`). The morphism of
models `τ : M'' ⟶ M'` of the geometric generic fibres
(`NearbyCyclesModel.traitSliceGenericSliceTraitHom`) therefore has invertible pullback exchange
with finite coefficients at complexes of étale origin, by the invariance of nearby cycles under
change of trait (SGA 4½, [Th. finitude], Prop. 3.7,
`ProEtale.CondensedRing.isIso_pullbackExchange_app_of_isPullback_trait_finite`):
`NearbyCyclesModel.isIso_pullbackExchange_traitSliceGenericSliceTraitHom_finite`.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

namespace GenericSliceTrait

variable {k' : Type u} [Field k'] (D : GenericSliceTrait k')

/-- The local injection `R ⟶ K⟦t⟧` restricts to the coefficientwise map on `k'⟦t⟧`. -/
lemma ι_comp_φ : D.ι.comp D.φ = PowerSeries.map (algebraMap k' (traitSliceField k')) := by
  have h : Spec.map (CommRingCat.ofHom (D.ι.comp D.φ)) =
      Spec.map (CommRingCat.ofHom (PowerSeries.map (algebraMap k' (traitSliceField k')))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, D.spec_φ, ← Category.assoc, D.spec_ι_comp,
      traitSlice_over]
    rfl
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/-- `t` is a uniformizer of `K⟦t⟧` coming from `R`: the change of trait `Spec K⟦t⟧ ⟶ S'` is
unramified. -/
lemma maximalIdeal_powerSeries_eq_map_ι :
    maximalIdeal (PowerSeries (traitSliceField k')) = (maximalIdeal D.R).map D.ι := by
  rw [D.maximalIdeal_eq, Ideal.map_map, ι_comp_φ,
    AlgebraicGeometry.maximalIdeal_powerSeries_eq_map k' (traitSliceField k')]

end GenericSliceTrait

namespace ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
  (b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k'))
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) (D : GenericSliceTrait k')

/-- The morphism of total spaces `𝒳 ×_{𝔸¹_S} T ⟶ 𝒳 ×_{𝔸¹_S} S'` of the slices, induced by the
factorisation `T ⟶ S' ⟶ 𝔸¹_S` of the generic slice. -/
noncomputable def traitSliceGenericSliceTraitTotal :
    pullback b (traitSlice (traitSliceCoord k')) ⟶ sliceTraitTotal D.toSliceTrait M b :=
  pullback.map b (traitSlice (traitSliceCoord k')) b D.toAffineLine (𝟙 _)
    (Spec.map (CommRingCat.ofHom D.ι)) (𝟙 _) (by simp) (by
      rw [Category.comp_id]
      exact D.spec_ι_comp.symm)

@[reassoc (attr := simp)]
lemma traitSliceGenericSliceTraitTotal_fst :
    traitSliceGenericSliceTraitTotal b D ≫ pullback.fst b D.toAffineLine = pullback.fst _ _ := by
  simp [traitSliceGenericSliceTraitTotal]

@[reassoc (attr := simp)]
lemma traitSliceGenericSliceTraitTotal_snd :
    traitSliceGenericSliceTraitTotal b D ≫ pullback.snd b D.toAffineLine =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.ι) := by
  simp [traitSliceGenericSliceTraitTotal]

/-- **The slice over `T` is the base change of the slice over `S'`**: the square of total
spaces over the change of traits `Spec K⟦t⟧ ⟶ S'` is cartesian. -/
lemma isPullback_traitSliceGenericSliceTraitTotal :
    IsPullback (traitSliceGenericSliceTraitTotal b D)
      (pullback.snd b (traitSlice (traitSliceCoord k')))
      (sliceTraitStructure D.toSliceTrait M b) (Spec.map (CommRingCat.ofHom D.ι)) := by
  have h : IsPullback (pullback.fst b (traitSlice (traitSliceCoord k')))
      (pullback.snd b (traitSlice (traitSliceCoord k'))) b
      (Spec.map (CommRingCat.ofHom D.ι) ≫ D.toAffineLine) := by
    rw [D.spec_ι_comp]
    exact IsPullback.of_hasPullback _ _
  refine IsPullback.of_right ?_ (traitSliceGenericSliceTraitTotal_snd b D)
    (IsPullback.of_hasPullback b D.toAffineLine)
  rw [traitSliceGenericSliceTraitTotal_fst]
  exact h

/-- The map `𝒳'' ×_T Spec Ω_K ⟶ 𝒳' ×_{S'} Spec Ω'` of geometric generic fibres of the slices,
induced by `D.ωK : Ω' ⟶ Ω_K`. -/
noncomputable def traitSliceGenericSliceTraitGeneric :
    (baseChange hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).generic ⟶
      (sliceTraitModel D.toSliceTrait M b).generic :=
  pullback.map _ _ _ _ (traitSliceGenericSliceTraitTotal b D)
    (Spec.map (CommRingCat.ofHom D.ωK)) (Spec.map (CommRingCat.ofHom D.ι))
    (traitSliceGenericSliceTraitTotal_snd b D).symm (by
      simp only [GenericSliceTrait.toSliceTrait_a, traitGenericPoint, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, D.ωK_comp_a])

@[reassoc (attr := simp)]
lemma traitSliceGenericSliceTraitGeneric_fst :
    traitSliceGenericSliceTraitGeneric hM b hb D ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ traitSliceGenericSliceTraitTotal b D :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma traitSliceGenericSliceTraitGeneric_snd :
    traitSliceGenericSliceTraitGeneric hM b hb D ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.ωK) :=
  pullback.lift_snd _ _ _

/-- The map `𝒳'' ×_T Spec K ⟶ 𝒳' ×_{S'} Spec κ'` of special fibres of the slices, induced by
`D.κK : κ' ⟶ K`. -/
noncomputable def traitSliceGenericSliceTraitSpecial :
    (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).left ⟶
      pullback (sliceTraitStructure D.toSliceTrait M b) (Spec.map (CommRingCat.ofHom D.b)) :=
  pullback.map _ _ _ _ (traitSliceGenericSliceTraitTotal b D)
    (Spec.map (CommRingCat.ofHom D.κK)) (Spec.map (CommRingCat.ofHom D.ι))
    (traitSliceGenericSliceTraitTotal_snd b D).symm (by
      simp only [traitClosedPoint, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, D.κK_comp_b])

@[reassoc (attr := simp)]
lemma traitSliceGenericSliceTraitSpecial_fst :
    traitSliceGenericSliceTraitSpecial b D ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ traitSliceGenericSliceTraitTotal b D :=
  pullback.lift_fst _ _ _

/-- **The change of trait `τ : M'' ⟶ M'` from the slice over `T` to the slice over `S'`**, on the
geometric models: `traitSliceGenericSliceTraitTotal` on total spaces and
`traitSliceGenericSliceTraitGeneric` on geometric generic fibres. -/
@[simps]
noncomputable def traitSliceGenericSliceTraitHom :
    (baseChange hM b hb (traitSlice (traitSliceCoord k')) (traitSlice_over _)).geometric.Hom
      (sliceTraitModel D.toSliceTrait M b) (traitSliceGenericSliceTraitTotal b D)
      (traitSliceGenericSliceTraitSpecial b D) where
  total := traitSliceGenericSliceTraitTotal b D
  generic := traitSliceGenericSliceTraitGeneric hM b hb D
  comm_j := traitSliceGenericSliceTraitGeneric_fst hM b hb D
  comm_i := traitSliceGenericSliceTraitSpecial_fst b D
  comm_ε := traitSliceGenericSliceTraitGeneric_fst hM b hb D

variable [IsSepClosed k'] [Fact (ringChar k').Prime]

set_option maxHeartbeats 1600000 in
-- debugging
/-- **Invariance of the nearby cycles of the slice under the change of trait `T ⟶ S'`**, finite
coefficients (SGA 4½, [Th. finitude], Prop. 3.7): the pullback exchange of the change of trait
`τ : M'' ⟶ M'` on the models of the geometric generic fibres is invertible at every complex `K`
on the geometric generic fibre of `M'` which is bounded below of étale origin, for a finite ring
`T₀` in which the characteristic `p` of `k'` is invertible. -/
theorem isIso_pullbackExchange_traitSliceGenericSliceTraitHom_finite
    (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀] [DiscreteTopology T₀]
    [Finite T₀] (hpT : IsUnit ((ringChar k' : ℕ) : T₀))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (sliceTraitModel D.toSliceTrait M b).generic) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T₀)
        (sliceTraitModel D.toSliceTrait M b).generic)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T₀))
      (sliceTraitModel D.toSliceTrait M b).generic
      ((finiteCoefficientDerivedEquivalence _ T₀).functor.obj K)) :
    IsIso (((traitSliceGenericSliceTraitHom hM b hb D).toGeneric.pullbackExchange
      (Profinite.continuousMapRingObj T₀)).app K) := by
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hM.isSeparated
  subst hb
  have : LocallyOfFiniteType b :=
    locallyOfFiniteType_of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have : QuasiCompact b := QuasiCompact.of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have : IsSeparated b := IsSeparated.of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have : LocallyOfFiniteType (sliceTraitStructure D.toSliceTrait M b) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback b D.toAffineLine) inferInstance
  have : QuasiCompact (sliceTraitStructure D.toSliceTrait M b) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback b D.toAffineLine) inferInstance
  have : IsSeparated (sliceTraitStructure D.toSliceTrait M b) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback b D.toAffineLine) inferInstance
  have hp : (ringChar k').Prime := Fact.out
  have hres : ∀ n : ℕ, (n : ResidueField D.R) = 0 → ringChar k' ∣ n := fun n hn ↦ by
    rw [← map_natCast (IsLocalRing.residue D.R), IsLocalRing.residue_eq_zero_iff, ← D.ker_b,
      RingHom.mem_ker, map_natCast] at hn
    rw [← D.ringChar_κ]
    exact ringChar.dvd hn
  let φ := traitSliceGenericSliceTraitHom hM b rfl D
  refine (Scheme.Hom.exists_locallyEmbedsInAffineSpace
    (sliceTraitStructure D.toSliceTrait M b)).elim fun m hm ↦ ?_
  have hw : (pullback.fst (pullback.snd b (traitSlice (traitSliceCoord k')))
      (traitClosedPoint (traitSliceField k')) ≫ φ.total) ≫
        sliceTraitStructure D.toSliceTrait M b =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom
        ((PowerSeries.constantCoeff (R := traitSliceField k')).comp D.ι)) := by
    rw [Category.assoc, ← (isPullback_traitSliceGenericSliceTraitTotal b D).w,
      pullback.condition_assoc, traitClosedPoint, CommRingCat.ofHom_comp, Spec.map_comp]
  have : Fact (ringChar k').Prime := ⟨hp⟩
  have h := (traitChangeInvariance T₀ m).isIso D.ι D.injective_ι
    D.maximalIdeal_powerSeries_eq_map_ι (ringChar k') hres hpT D.a
    (algebraMap (PowerSeries (traitSliceField k')) (traitGenericField (traitSliceField k')))
    D.ωK D.injective_a (algebraMap_traitGenericField_injective _) D.isAlgebraic_a
    (isAlgebraic_traitGenericField _) D.ωK_comp_a PowerSeries.constantCoeff
    PowerSeries.ker_coeff_eq_max_ideal
    (φ.toGenericWithSpecial (pullback.fst _ _) (pullback.lift
      (pullback.fst (pullback.snd b (traitSlice (traitSliceCoord k')))
        (traitClosedPoint (traitSliceField k')) ≫ φ.total) (pullback.snd _ _) hw)
      (pullback.lift_fst _ _ _))
    (sliceTraitStructure D.toSliceTrait M b) inferInstance inferInstance inferInstance hm
    (pullback.snd _ _) (isPullback_sliceTraitModel_j D.toSliceTrait M b)
    (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    (pullback.snd _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    (isPullback_traitSliceGenericSliceTraitTotal b D)
    (traitSliceGenericSliceTraitGeneric_snd hM b rfl D) (pullback.lift_snd _ _ _) K (by exact_mod_proofs hK)
  have h' := Hom.isIso_map_exchangeRight_app_of_isIso_pullbackExchange_toGenericWithSpecial
    _ φ _ _ _ K h
  have h₃ := Hom.isIso_pullbackExchange_app_of_isIso_map_exchangeRight_app _ φ.toGeneric K
    (by transport_exact h')
  exact_mod_proofs h₃

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
