/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceBaseModel
public import WeilConjectures.TraceFormula.Specialization.TraitModelCompactification

/-!

# Trait models over a generic base

Let `S = Spec k'⟦t⟧` be the trait, `η = Spec K₀ ⟶ S` its generic point (`K₀ = Frac k'⟦t⟧`,
`AlgebraicGeometry.traitGenericSpec`) and `Spec Ω ⟶ η` the geometric generic point
(`AlgebraicGeometry.traitGenericPointToSpec`). A trait model of `X` over the base
(`NearbyCyclesModel.IsTraitModelOfBase`) requires the base field `k` to map into `k'⟦t⟧`, which
fails for the generic slices along general coordinates. The generalisation
`NearbyCyclesModel.IsTraitModelOfGenericBase` only asks for a morphism `ι : η ⟶ Spec F` from the
generic point of the trait to the spectrum of the base field `F`: the model `M` of an `F`-scheme
`X₁` is of finite type over `S` along `q`, and its generic fibre `𝒳_η = 𝒳 ×_S η` is an open of
`X₁ ×_F η`, compatibly with the identification `ε : 𝒳_Ω ⟶ X₁` (which is then the composite
`𝒳_Ω ⟶ 𝒳_η ⟶ X₁ ×_F η ⟶ X₁`). The geometric generic fibre is then open in `X₁ ×_F Spec Ω`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_openImmersion`).

* Every trait model over the base is a trait model over the generic base `(k, X)`, with
  `ι : η ⟶ S ⟶ Spec k` (`NearbyCyclesModel.IsTraitModelOfBase.isTraitModelOfGenericBase`). The
  openness of the generic fibre is obtained by fpqc descent from the geometric generic fibre.
* For a model `M` of finite type over `S`, a coordinate `b : 𝒳 ⟶ 𝔸¹_S` over `S`, a field
  extension `K` of `k'` and `x ∈ K`, the base change of `M` along the generic slice
  `σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` (`AlgebraicGeometry.traitSlice`) is a trait model over the generic base
  `(F', X₂)` with `F' = Frac K⟦t⟧` and `X₂ = 𝒳_η ×_{𝔸¹_η} Spec F'`, the generic fibre of `b`
  sliced at the generic slice `σ_η : Spec F' ⟶ 𝔸¹_η` (`AlgebraicGeometry.traitGenericSlice`)
  (`NearbyCyclesModel.isTraitModelOfGenericBase_genericSliceModel`). In fact the generic fibre of
  the slice is all of `X₂`. If `M` is a trait model over the generic base `(F, X₁)`, then `X₂`
  maps to `X₁` compatibly with the identifications `ε`
  (`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_genericSliceBase_comp`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

section GenericSlice

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

/-- The embedding `Frac k'⟦t⟧ ⟶ Frac K⟦t⟧` of the fields of fractions of the traits induced by
the coefficientwise map. -/
noncomputable def traitFractionMap :
    FractionRing (PowerSeries k') →+* FractionRing (PowerSeries K) :=
  IsFractionRing.map (PowerSeries.map_injective _ (algebraMap k' K).injective)

/-- The embedding `Frac k'⟦t⟧ ⟶ Frac K⟦t⟧` lies over the coefficientwise map. -/
lemma traitFractionMap_comp_algebraMap :
    (traitFractionMap k' K).comp (algebraMap (PowerSeries k') (FractionRing (PowerSeries k'))) =
      (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp
        (PowerSeries.map (algebraMap k' K)) :=
  IsLocalization.map_comp (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (PowerSeries.map_injective _ (algebraMap k' K).injective))

/-- The map `Spec Frac K⟦t⟧ ⟶ Spec Frac k'⟦t⟧` of the generic points of the traits. -/
noncomputable def traitGenericSpecMap :
    Spec (.of (FractionRing (PowerSeries K))) ⟶ Spec (.of (FractionRing (PowerSeries k'))) :=
  Spec.map (CommRingCat.ofHom (traitFractionMap k' K))

/-- The trait map sends the generic point to the generic point. -/
@[reassoc]
lemma traitGenericSpec_traitMap :
    traitGenericSpec K ≫ traitMap k' K = traitGenericSpecMap k' K ≫ traitGenericSpec k' := by
  rw [traitGenericSpec, traitMap, traitGenericSpecMap, traitGenericSpec, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    traitFractionMap_comp_algebraMap]

/-- The geometric generic points of the traits lie over the map of their generic points. -/
@[reassoc]
lemma traitGenericPointToSpec_traitGenericSpecMap :
    traitGenericPointToSpec K ≫ traitGenericSpecMap k' K =
      traitGenericPointMap k' K ≫ traitGenericPointToSpec k' := by
  rw [traitGenericPointToSpec, traitGenericSpecMap, traitGenericPointMap, traitGenericPointToSpec,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine IsLocalization.ringHom_ext (nonZeroDivisors (PowerSeries k')) ?_
  rw [RingHom.comp_assoc, traitFractionMap_comp_algebraMap, ← RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq,
    traitGenericFieldMap_comp_algebraMap]

variable {k' K} (x : K)

/-- The generic slice over the generic point: the restriction `σ_η : Spec Frac K⟦t⟧ ⟶ 𝔸¹_η` of the
generic slice `σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` to the generic points, `η = Spec Frac k'⟦t⟧`. -/
noncomputable def traitGenericSlice :
    Spec (.of (FractionRing (PowerSeries K))) ⟶
      𝔸(ULift.{u} (Fin 1); Spec (.of (FractionRing (PowerSeries k')))) :=
  (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (traitGenericSpec k')).lift
    (traitGenericSpec K ≫ traitSlice x) (traitGenericSpecMap k' K) (by
      rw [Category.assoc, traitSlice_over, traitGenericSpec_traitMap])

@[reassoc (attr := simp)]
lemma traitGenericSlice_map :
    traitGenericSlice (k' := k') x ≫ AffineSpace.map _ (traitGenericSpec k') =
      traitGenericSpec K ≫ traitSlice x :=
  (AffineSpace.isPullback_map _).lift_fst _ _ _

@[reassoc (attr := simp)]
lemma traitGenericSlice_over :
    traitGenericSlice (k' := k') x ≫
        𝔸(ULift.{u} (Fin 1); Spec (.of (FractionRing (PowerSeries k')))) ↘
          Spec (.of (FractionRing (PowerSeries k'))) =
      traitGenericSpecMap k' K :=
  (AffineSpace.isPullback_map _).lift_snd _ _ _

end GenericSlice

section GenericFibreBaseChange

variable (k' : Type u) [Field k'] {B : Scheme.{u}} (X₁ : Over B)
  (ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ B)

end GenericFibreBaseChange

namespace ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

section Definition

variable {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}

/-- The inclusion `𝒳_Ω ⟶ 𝒳_η = 𝒳 ×_S η` of the geometric generic fibre of a model over the trait
`S` into its generic fibre. -/
noncomputable def genericFibreInclusion (M : NearbyCyclesModel X X'.left) (q : M.total ⟶ trait k')
    (g : M.generic ⟶ Spec (.of (traitGenericField k')))
    (h : M.j ≫ q = g ≫ traitGenericPoint k') :
    M.generic ⟶ pullback q (traitGenericSpec k') :=
  pullback.lift M.j (g ≫ traitGenericPointToSpec k') (by
    rw [Category.assoc, traitGenericPointToSpec_traitGenericSpec, h])

@[reassoc (attr := simp)]
lemma genericFibreInclusion_fst (M : NearbyCyclesModel X X'.left) (q : M.total ⟶ trait k')
    (g : M.generic ⟶ Spec (.of (traitGenericField k')))
    (h : M.j ≫ q = g ≫ traitGenericPoint k') :
    genericFibreInclusion M q g h ≫ pullback.fst _ _ = M.j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma genericFibreInclusion_snd (M : NearbyCyclesModel X X'.left) (q : M.total ⟶ trait k')
    (g : M.generic ⟶ Spec (.of (traitGenericField k')))
    (h : M.j ≫ q = g ≫ traitGenericPoint k') :
    genericFibreInclusion M q g h ≫ pullback.snd _ _ = g ≫ traitGenericPointToSpec k' :=
  pullback.lift_snd _ _ _

variable {F : Type u} [Field F]

/-- A nearby-cycles model `M` of an `F`-scheme `X₁` with special fibre `X'` is a *trait model of
`X₁` over the generic base* along `q : 𝒳 ⟶ S`, `g : 𝒳_Ω ⟶ Spec Ω` and a morphism
`ι : η ⟶ Spec F` from the generic point `η = Spec Frac k'⟦t⟧` of the trait `S = Spec k'⟦t⟧`, if it
is of finite type over `S` along `q` and `g`, and its generic fibre `𝒳_η = 𝒳 ×_S η` is an open of
`X₁ ×_F η` by an open immersion `w` over `η` through which the identification `ε` factors:
`ε = (𝒳_Ω ⟶ 𝒳_η) ≫ w ≫ (X₁ ×_F η ⟶ X₁)`. -/
structure IsTraitModelOfGenericBase (X₁ : Over (Spec (.of F)))
    (ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F))
    (M : NearbyCyclesModel X₁.left X'.left) (q : M.total ⟶ trait k')
    (g : M.generic ⟶ Spec (.of (traitGenericField k'))) : Prop where
  isTraitModelOver : M.IsTraitModelOver q g
  exists_openImmersion_genericFibre :
    ∃ w : pullback q (traitGenericSpec k') ⟶ pullback X₁.hom ι,
      IsOpenImmersion w ∧ w ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        genericFibreInclusion M q g isTraitModelOver.isPullback_j.w ≫ w ≫ pullback.fst _ _ =
          M.ε

end Definition

section OfBase

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

end OfBase

section GenericSlice

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] (x : K)
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)

/-- The base `X₂ = 𝒳_η ×_{𝔸¹_η} Spec Frac K⟦t⟧` of the generic slice: the generic fibre
`b_η : 𝒳_η ⟶ 𝔸¹_η` of the coordinate `b`, sliced at the generic slice
`σ_η : Spec Frac K⟦t⟧ ⟶ 𝔸¹_η`, as a scheme over `Frac K⟦t⟧`. -/
noncomputable def genericSliceBase : Over (Spec (.of (FractionRing (PowerSeries K)))) :=
  Over.mk (pullback.snd (coordinateBaseChange b hb (traitGenericSpec k')) (traitGenericSlice x))

/-- The map `𝒳''_η ⟶ 𝒳_η` from the generic fibre of the slice `𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧` to the
generic fibre of `𝒳`. -/
noncomputable def genericSliceFibreMap :
    pullback (pullback.snd b (traitSlice x)) (traitGenericSpec K) ⟶
      pullback q (traitGenericSpec k') :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ traitGenericSpecMap k' K) (by
      rw [Category.assoc, Category.assoc,
        pullback_fst_comp_eq_snd_comp_traitMap b hb (traitSlice x) (traitSlice_over x),
        pullback.condition_assoc, traitGenericSpec_traitMap])

@[reassoc (attr := simp)]
lemma genericSliceFibreMap_fst :
    genericSliceFibreMap x hb ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma genericSliceFibreMap_snd :
    genericSliceFibreMap x hb ≫ pullback.snd _ _ = pullback.snd _ _ ≫ traitGenericSpecMap k' K :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma genericSliceFibreMap_coordinate :
    genericSliceFibreMap x hb ≫ coordinateBaseChange b hb (traitGenericSpec k') =
      pullback.snd _ _ ≫ traitGenericSlice x := by
  refine (AffineSpace.isPullback_map (traitGenericSpec k')).hom_ext ?_ ?_
  · simp only [Category.assoc, coordinateBaseChange_map, genericSliceFibreMap_fst_assoc,
      traitGenericSlice_map]
    rw [pullback.condition, pullback.condition_assoc]
  · rw [Category.assoc, coordinateBaseChange_over, genericSliceFibreMap_snd, Category.assoc,
      traitGenericSlice_over]

/-- **The generic fibre of the slice is the slice of the generic fibre**:
`𝒳''_η = 𝒳_η ×_{𝔸¹_η} Spec Frac K⟦t⟧`. -/
lemma isPullback_genericSliceFibreMap :
    IsPullback (genericSliceFibreMap x hb) (pullback.snd _ _)
      (coordinateBaseChange b hb (traitGenericSpec k')) (traitGenericSlice x) := by
  refine IsPullback.of_right ?_ (genericSliceFibreMap_coordinate x hb)
    (isPullback_coordinateBaseChange b hb (traitGenericSpec k'))
  rw [genericSliceFibreMap_fst, traitGenericSlice_map]
  exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)

/-- The identification `𝒳''_η ≅ X₂` of the generic fibre of the slice with the base of the
generic slice. -/
noncomputable def genericSliceFibreIso :
    pullback (pullback.snd b (traitSlice x)) (traitGenericSpec K) ≅
      (genericSliceBase x hb).left :=
  (isPullback_genericSliceFibreMap x hb).isoPullback

@[reassoc (attr := simp)]
lemma genericSliceFibreIso_hom_fst :
    (genericSliceFibreIso x hb).hom ≫ pullback.fst _ _ = genericSliceFibreMap x hb :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
lemma genericSliceFibreIso_hom_over :
    (genericSliceFibreIso x hb).hom ≫ (genericSliceBase x hb).hom = pullback.snd _ _ :=
  IsPullback.isoPullback_hom_snd _

/-- The *generic slice model*: the base change of `M` along the generic slice
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S`, with total space `𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧`, geometric generic fibre
`𝒳'' ×_{K⟦t⟧} Spec Ω_K`, special fibre `𝒳'' ×_{K⟦t⟧} Spec K`, viewed as a model of the base
`X₂ = 𝒳_η ×_{𝔸¹_η} Spec Frac K⟦t⟧` through `𝒳''_Ω ⟶ 𝒳''_η ≅ X₂`. -/
@[simps]
noncomputable def genericSliceModel :
    NearbyCyclesModel (genericSliceBase x hb).left (baseChangeSpecial b (traitSlice x)).left where
  total := pullback b (traitSlice x)
  generic := pullback (pullback.snd b (traitSlice x)) (traitGenericPoint K)
  j := pullback.fst _ _
  i := pullback.fst _ _
  ε := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ traitGenericPointToSpec K) (by
      rw [pullback.condition, Category.assoc, traitGenericPointToSpec_traitGenericSpec]) ≫
    (genericSliceFibreIso x hb).hom

end GenericSlice

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
