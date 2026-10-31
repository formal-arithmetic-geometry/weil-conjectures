/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.AffineCharts
public import WeilConjectures.TraceFormula.Specialization.CoordinateCompactificationProjective
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSlice
public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceShrink
import WeilConjectures.Tactic.TransportExact

/-!

# The twist equation for quasi-projective opens

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

/-- The field of fractions of a polynomial ring over `K` has the characteristic of `K`. -/
lemma ringChar_fractionRing_mvPolynomial (σ : Type u) (K : Type u) [Field K] :
    ringChar (FractionRing (MvPolynomial σ K)) = ringChar K :=
  (Algebra.ringChar_eq K (FractionRing (MvPolynomial σ K))).symm

instance instFactPrimeRingCharFractionRingMvPolynomial (σ : Type u) (K : Type u) [Field K]
    [Fact (ringChar K).Prime] : Fact (ringChar (FractionRing (MvPolynomial σ K))).Prime :=
  ⟨by rw [ringChar_fractionRing_mvPolynomial]; exact Fact.out⟩

instance instFactRingCharFractionRingMvPolynomialNe (σ : Type u) (K : Type u) [Field K] (ℓ : ℕ)
    [Fact (ringChar K ≠ ℓ)] : Fact (ringChar (FractionRing (MvPolynomial σ K)) ≠ ℓ) :=
  ⟨by rw [ringChar_fractionRing_mvPolynomial]; exact Fact.out⟩

namespace ProEtale.CondensedRing

open Scheme

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

-- a second instance path to the field structure of `Frac k'⟦t⟧` when `k'` is separably closed
attribute [-instance] AlgebraicGeometry.Scheme.isStrictlyHenselianLocalRing_of_isSepClosed

namespace NearbyCyclesModel

section Compactified

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {Xc : Over (Spec (@CommRingCat.of (FractionRing (PowerSeries k')) Field.toCommRing))}
  [LocallyOfFiniteType Xc.hom] [QuasiCompact Xc.hom] [IsSeparated Xc.hom]
  [IsProper (CondensedRing.toPoint Xc).left]
  {Xc' : Over (Spec (.of k'))} [LocallyOfFiniteType Xc'.hom] [QuasiCompact Xc'.hom]
  [IsSeparated Xc'.hom] [IsProper (CondensedRing.toPoint Xc').left]
  {N : NearbyCyclesModel Xc.left Xc'.left} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}
  {Y₁ : Over (Spec (@CommRingCat.of (FractionRing (PowerSeries k')) Field.toCommRing))}
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  {Y₂ : Over (Spec (.of k'))} [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom]
  [IsSeparated Y₂.hom]
  {i₁ : Xc ⟶ Y₁} {p₁ : Y₁ ⟶ overProjectiveLine (point (FractionRing (PowerSeries k')))}
  {i₂ : Xc' ⟶ Y₂} {p₂ : Y₂ ⟶ overProjectiveLine (point k')}
  (bc : N.Hom (projectiveLineModel k') (i₁ ≫ p₁).left (i₂ ≫ p₂).left)
  {U : N.total.Opens} [QuasiCompact U.ι]
  {bW : (N.restrictOpen U).total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hbW : bW ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = U.ι ≫ qN)

include bc in
/-- The total space of the generic slice of `W = b̄⁻¹(𝔸¹_S)` is proper over the slice trait. -/
lemma isProper_pullback_snd_traitSlice_of_compactified [IsProper qN]
    (hU : U = bc.total ⁻¹ᵁ (coordChart (trait k')).opensRange)
    (hbWχ : bW ≫ coordChart (trait k') = U.ι ≫ bc.total)
    (hqN : qN = bc.total ≫ (ProjectiveLine (trait k') ↘ trait k')) :
    IsProper (pullback.snd bW (traitSlice (traitSliceCoord k'))) := by
  have : IsProper (bc.total ≫ (ProjectiveLine (trait k') ↘ trait k')) := hqN ▸ inferInstance
  have : IsProper bc.total := IsProper.of_comp bc.total (ProjectiveLine (trait k') ↘ trait k')
  exact MorphismProperty.of_isPullback (P := @IsProper)
    (isPullback_genericSlice_projectiveLineSlice (traitSliceCoord k') bc hU hbWχ).flip
    inferInstance


variable [LocallyOfFiniteType (N.restrictSpecialFibre U).hom]
  [QuasiCompact (N.restrictSpecialFibre U).hom] [IsSeparated (N.restrictSpecialFibre U).hom]
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hbW).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hbW).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hbW).hom]
  [IsProper (CondensedRing.toPoint (genericSliceBase (traitSliceCoord k') hbW)).left]
  [LocallyOfFiniteType (baseChangeSpecial bW (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial bW (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial bW (traitSlice (traitSliceCoord k'))).hom]
  [IsProper (CondensedRing.toPoint (baseChangeSpecial bW (traitSlice (traitSliceCoord k')))).left]

/-- **The twist equation of a compactified model along the slice of `W = b̄⁻¹(𝔸¹_S)`**: for a
proper trait model `N` over `(η, X̄₁, 𝟙)` with full geometric generic fibre, a proper morphism of
models `b̄ : N ⟶ ℙ¹_S` whose maps of fibres are projective (`b̄₁ = i₁ ≫ p₁`, `b̄₂ = i₂ ≫ p₂`),
and the coordinate `b_W` of `W = b̄⁻¹(𝔸¹_S)`, the twist equation holds for `θ_N` along the
composite `W'' ⟶ W ⟶ N` of the slice projection and the inclusion
(`NearbyCyclesModel.exists_twist_of_slice_of_composition_law` for `P = ℙ¹_S`, whose own twist
equation is `NearbyCyclesModel.exists_twist_projectiveLineSlice`). -/
theorem exists_twist_genericSliceCompHom (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ)
    (hN : N.IsTraitModelOfGenericBase Xc (𝟙 _) qN gN) [IsProper qN]
    (hNgen : IsPullback N.ε gN Xc.hom (traitGenericPointToSpec k' ≫ 𝟙 _)) {d : ℕ}
    [IsClosedImmersion i₁.left] [IsProper p₁.left] [SmoothOfRelativeDimension d p₁.left]
    [IsClosedImmersion i₂.left] [IsProper p₂.left] [SmoothOfRelativeDimension d p₂.left]
    (hqN : qN = bc.total ≫ (ProjectiveLine (trait k') ↘ trait k'))
    (hgN : gN = bc.generic ≫
      (ProjectiveLine (Spec (.of (traitGenericField k'))) ↘ Spec (.of (traitGenericField k'))))
    (hU : U = bc.total ⁻¹ᵁ (coordChart (trait k')).opensRange)
    (hbWχ : bW ≫ coordChart (trait k') = U.ι ≫ bc.total)
    [IsProper (pullback.snd bW (traitSlice (traitSliceCoord k')))]
    [IsProper (genericSliceBaseToPoint (traitSliceCoord k') hbW).left]
    [IsProper (baseChangeSpecialToPoint (b := bW) (traitSliceCoord k')).left] :
    ∃ (u : (IsTraitModelOfGenericBase.genericSliceUpperStarComp ℓ (hN.restrictOpen U) hbW
          (𝟙 Xc)).obj (dualizingComplex ℓ Xc) ≅
        dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hbW) ⊗
          boundedConstructibleTateTwist ℓ (genericSliceBase (traitSliceCoord k') hbW) 0 2)
      (v : (IsTraitModelOfGenericBase.sliceSpecialUpperStarComp ℓ (hN.restrictOpen U) hbW
          (N.restrictSpecialFibreι U)).obj (dualizingComplex ℓ Xc') ≅
        dualizingComplex ℓ (baseChangeSpecial bW (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ
            (baseChangeSpecial bW (traitSlice (traitSliceCoord k'))) 0 2),
      (IsTraitModelOfGenericBase.sliceSpecialUpperStarComp ℓ (hN.restrictOpen U) hbW
          (N.restrictSpecialFibreι U)).map (D.θ hN) ≫ v.hom =
        (IsTraitModelOfGenericBase.genericSliceExchangeComp ℓ (hN.restrictOpen U) hbW hN (𝟙 Xc)
            (N.restrictSpecialFibreι U) (N.restrictOpenHom U)).app (dualizingComplex ℓ Xc) ≫
          (IsTraitModelOfGenericBase.genericSliceNearbyCycles (traitSliceCoord k') ℓ
            (hN.restrictOpen U) hbW).map u.hom ≫
          (IsTraitModelOfGenericBase.genericSliceTwistIso ℓ (hN.restrictOpen U) hbW _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hbW
            (hN.restrictOpen U).isTraitModelOver) ▷ _ := by
  have hx := transcendental_traitSliceCoord k'
  have : IsProper (i₁ ≫ p₁).left := inferInstanceAs (IsProper (i₁.left ≫ p₁.left))
  have : IsProper (i₂ ≫ p₂).left := inferInstanceAs (IsProper (i₂.left ≫ p₂.left))
  have hbsq := isPullback_genericSliceCompHom_generic (hN := hN) (traitSliceCoord k') bc hbW hU
    hbWχ hqN hNgen
  have hssq := isPullback_genericSliceCompHom_special (hN := hN) (traitSliceCoord k') bc hbW hU
    hbWχ hqN
  have := isIso_upperShriekBaseChangeOfMap_projectiveLineGenericSlice ℓ hx i₁ p₁ hbsq
  have := isIso_upperShriekBaseChangeOfMap_projectiveLineSpecialSlice ℓ hx i₂ p₂ hssq
  have HP := exists_twist_projectiveLineSlice (ℓ := ℓ) (traitSliceCoord k') D DK
  obtain ⟨u, v, huv⟩ := exists_twist_of_slice_of_composition_law D DK hN
    hNgen (isTraitModelOfGenericBase_projectiveLineModel k')
    (isPullback_projectiveLineModel_ε k')
    (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hbW
      (hN.restrictOpen U).isTraitModelOver)
    (isPullback_genericSliceModel_ε (traitSliceCoord k') hbW (hN.restrictOpen U).isTraitModelOver)
    (isTraitModelOfGenericBase_sliceTraitModel (traitSliceField k'))
    (isPullback_sliceTraitModel_ε (traitSliceField k')) (i₁ ≫ p₁) (i₂ ≫ p₂) bc hqN hgN
    (genericSliceBaseToPoint (traitSliceCoord k') hbW)
    (baseChangeSpecialToPoint (b := bW) (traitSliceCoord k'))
    (genericSliceTraitHom (traitSliceCoord k') hbW) (Category.comp_id _).symm
    (Category.comp_id _).symm (genericSliceCompHom (traitSliceCoord k') hN hbW)
    (projectiveLineSliceHom (traitSliceCoord k'))
    (genericSliceCompHom_total_comp (traitSliceCoord k') bc hbW hbWχ)
    (genericSliceCompHom_generic_comp (traitSliceCoord k') bc hbW hbWχ hgN) hbsq hssq HP
  exact ⟨u, v, huv⟩


/-- **The twist equation for `W = b̄⁻¹(𝔸¹_S)`**: in the situation of
`NearbyCyclesModel.exists_twist_genericSliceCompHom`, the twist equation of
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel_comp`
holds for the open sub-model `W = N|_U` and its coordinate `b_W`. -/
theorem exists_twist_restrictOpen_of_compactified (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ)
    (hN : N.IsTraitModelOfGenericBase Xc (𝟙 _) qN gN) [IsProper qN]
    (hNgen : IsPullback N.ε gN Xc.hom (traitGenericPointToSpec k' ≫ 𝟙 _)) {d : ℕ}
    [IsClosedImmersion i₁.left] [IsProper p₁.left] [SmoothOfRelativeDimension d p₁.left]
    [IsClosedImmersion i₂.left] [IsProper p₂.left] [SmoothOfRelativeDimension d p₂.left]
    (hqN : qN = bc.total ≫ (ProjectiveLine (trait k') ↘ trait k'))
    (hgN : gN = bc.generic ≫
      (ProjectiveLine (Spec (.of (traitGenericField k'))) ↘ Spec (.of (traitGenericField k'))))
    (hU : U = bc.total ⁻¹ᵁ (coordChart (trait k')).opensRange)
    (hbWχ : bW ≫ coordChart (trait k') = U.ι ≫ bc.total)
    [IsProper (pullback.snd bW (traitSlice (traitSliceCoord k')))]
    [IsProper (genericSliceBaseToPoint (traitSliceCoord k') hbW).left]
    [IsProper (baseChangeSpecialToPoint (b := bW) (traitSliceCoord k')).left] :
    ∃ (u : (IsTraitModelOfGenericBase.genericSliceUpperStar (traitSliceCoord k') ℓ
          (hN.restrictOpen U) hbW).obj (dualizingComplex ℓ Xc) ≅
        dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hbW) ⊗
          boundedConstructibleTateTwist ℓ (genericSliceBase (traitSliceCoord k') hbW) 0 2)
      (v : (IsTraitModelOfGenericBase.sliceSpecialUpperStar (traitSliceCoord k') ℓ
          (hN.restrictOpen U) hbW).obj (dualizingComplex ℓ (N.restrictSpecialFibre U)) ≅
        dualizingComplex ℓ (baseChangeSpecial bW (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ
            (baseChangeSpecial bW (traitSlice (traitSliceCoord k'))) 0 2),
      (IsTraitModelOfGenericBase.sliceSpecialUpperStar (traitSliceCoord k') ℓ
          (hN.restrictOpen U) hbW).map (D.θ (hN.restrictOpen U)) ≫ v.hom =
        (IsTraitModelOfGenericBase.genericSliceExchange (traitSliceCoord k') ℓ
            (hN.restrictOpen U) hbW).app (dualizingComplex ℓ Xc) ≫
          (IsTraitModelOfGenericBase.genericSliceNearbyCycles (traitSliceCoord k') ℓ
            (hN.restrictOpen U) hbW).map u.hom ≫
          (IsTraitModelOfGenericBase.genericSliceTwistIso ℓ (hN.restrictOpen U) hbW _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hbW
            (hN.restrictOpen U).isTraitModelOver) ▷ _ := by
  have : IsOpenImmersion (Over.Hom.left (𝟙 Xc)) := inferInstanceAs (IsOpenImmersion (𝟙 _))
  have : IsOpenImmersion (N.restrictOpenHom U).total := inferInstanceAs (IsOpenImmersion U.ι)
  exact IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel_comp ℓ
    (hN.restrictOpen U) hbW hN (𝟙 Xc) (N.restrictSpecialFibreι U) (N.restrictOpenHom U) D DK
    (isPullback_morphismRestrict N.j U).flip rfl rfl
    (exists_twist_genericSliceCompHom bc hbW D DK hN hNgen hqN hgN hU hbWχ)


end Compactified

section QuasiProjective

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X₁ : Over (Spec (@CommRingCat.of (FractionRing (PowerSeries k')) Field.toCommRing))}
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]

/-- **The twist equation for a quasi-projective model over `(η, X₁, 𝟙)`** (blueprint
`det-tf-nearby-duality-slice`, "the map `θ`"): let `M` be a trait model over the generic base
`(η, X₁, 𝟙)` with full generic fibre, whose total space is quasi-projective over `S`
(an immersion `e : 𝒳 ⟶ ℙ(n; S)` over `S`), and `b` a coordinate of `M`. Then the twist equation
of `NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel` holds
for `M` and `b`.

`M` is an open sub-model of `W = b̄⁻¹(𝔸¹_S)` for the projective compactification `b̄ : N ⟶ ℙ¹_S`
of `b` (`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_projectiveCoordinateCompactification`),
whose twist equation is `NearbyCyclesModel.exists_twist_restrictOpen_of_compactified`; open
restriction (`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel`)
passes it to `M`. -/
theorem exists_twist_of_isImmersion (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ)
    (h : M.IsTraitModelOfGenericBase X₁ (𝟙 _) q g)
    (hfull : ∃ w : pullback q (traitGenericSpec k') ⟶ pullback X₁.hom (𝟙 _), IsIso w ∧
      w ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      genericFibreInclusion M q g h.isTraitModelOver.isPullback_j.w ≫ w ≫ pullback.fst _ _ = M.ε)
    {n : Type u} [Finite n] {d : ℕ} (hn : Nat.card n = d + 1) (e : M.total ⟶ ℙ(n; trait k'))
    [IsImmersion e] (he : e ≫ ℙ(n; trait k') ↘ trait k' = q) :
    ∃ (u : (IsTraitModelOfGenericBase.genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj
          (dualizingComplex ℓ X₁) ≅
        dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hb) ⊗
          boundedConstructibleTateTwist ℓ (genericSliceBase (traitSliceCoord k') hb) 0 2)
      (v : (IsTraitModelOfGenericBase.sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj
          (dualizingComplex ℓ X') ≅
        dualizingComplex ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k'))) ⊗
          boundedConstructibleTateTwist ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k')))
            0 2),
      (IsTraitModelOfGenericBase.sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).map
          (D.θ h) ≫ v.hom =
        (IsTraitModelOfGenericBase.genericSliceExchange (traitSliceCoord k') ℓ h hb).app
            (dualizingComplex ℓ X₁) ≫
          (IsTraitModelOfGenericBase.genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).map
            u.hom ≫
          (IsTraitModelOfGenericBase.genericSliceTwistIso ℓ h hb _).hom ≫
          DK.θ (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
            h.isTraitModelOver) ▷ _ := by
  obtain ⟨Xc, _, _, _, _, Xc', _, _, _, _, N, qN, gN, hN, _, hNgen, b₁, _, b₂, _, bc, hqN, hgN, U,
    hU, _, _, _, _, bW, hbW, hbWχ, j, _, j', _, φ, _, Y₁, _, _, _, i₁, p₁, Y₂, _, _, _, i₂, p₂,
    hφ, hq, hg, hbb, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩ :=
    h.exists_projectiveCoordinateCompactification hfull hb hn e he
  -- the slice of `W = b̄⁻¹(𝔸¹_S)` is proper over the slice trait, with proper fibres
  have hbsq := isPullback_genericSliceCompHom_generic (hN := hN) (traitSliceCoord k') bc hbW hU
    hbWχ hqN hNgen
  have hssq := isPullback_genericSliceCompHom_special (hN := hN) (traitSliceCoord k') bc hbW hU
    hbWχ hqN
  have : IsProper (i₁ ≫ p₁).left := inferInstanceAs (IsProper (i₁.left ≫ p₁.left))
  have : IsProper (i₂ ≫ p₂).left := inferInstanceAs (IsProper (i₂.left ≫ p₂.left))
  have : IsProper (genericSliceBaseToPoint (traitSliceCoord k') hbW).left :=
    MorphismProperty.of_isPullback (P := @IsProper) hbsq inferInstance
  have : IsProper (baseChangeSpecialToPoint (b := bW) (traitSliceCoord k')).left :=
    MorphismProperty.of_isPullback (P := @IsProper) hssq inferInstance
  have : IsProper (pullback.snd bW (traitSlice (traitSliceCoord k'))) :=
    isProper_pullback_snd_traitSlice_of_compactified bc hbW hU hbWχ hqN
  have h₁ : IsProper (genericSliceBase (traitSliceCoord k') hbW).hom :=
    inferInstanceAs (IsProper (genericSliceBaseToPoint (traitSliceCoord k') hbW).left)
  have h₂ : IsProper (baseChangeSpecial bW (traitSlice (traitSliceCoord k'))).hom :=
    inferInstanceAs (IsProper (baseChangeSpecialToPoint (b := bW) (traitSliceCoord k')).left)
  have : IsProper (CondensedRing.toPoint (genericSliceBase (traitSliceCoord k') hbW)).left := by
    rw [toPoint_left]; exact h₁
  have : IsProper (CondensedRing.toPoint
      (baseChangeSpecial bW (traitSlice (traitSliceCoord k')))).left := by
    rw [toPoint_left]; exact h₂
  have HW := exists_twist_restrictOpen_of_compactified bc hbW D DK hN hNgen hqN hgN hU hbWχ
  exact IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_of_openSubmodel ℓ h hb
    (hN.restrictOpen U) hbW D DK j j' φ hφ hq hg hbb HW

end QuasiProjective


namespace IsTraitModelOfGenericBase

variable {F : Type u} [Field F] {k' : Type u} [Field k']
  {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {Xc : Over (Spec (.of F))} {Xc' : Over (Spec (.of k'))}
  {Mc : NearbyCyclesModel Xc.left Xc'.left} {qc : Mc.total ⟶ trait k'}
  {gc : Mc.generic ⟶ Spec (.of (traitGenericField k'))}
  (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType Xc.hom] [QuasiCompact Xc.hom] [IsSeparated Xc.hom]
  [LocallyOfFiniteType Xc'.hom] [QuasiCompact Xc'.hom] [IsSeparated Xc'.hom]
  [IsProper (CondensedRing.toPoint Xc).left] [IsProper (CondensedRing.toPoint Xc').left]
  (hMc : Mc.IsTraitModelOfGenericBase Xc ι qc gc) [IsProper qc]
  (V : Mc.total.Opens) [QuasiCompact V.ι]
  [LocallyOfFiniteType (Mc.restrictSpecialFibre V).hom]
  [QuasiCompact (Mc.restrictSpecialFibre V).hom] [IsSeparated (Mc.restrictSpecialFibre V).hom]
  {b : (Mc.restrictOpen V).total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = V.ι ≫ qc)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]

/-- **The twist equation for the opens of the induction** (blueprint
`det-tf-nearby-duality-slice`, "the twist (1)" and "the map `θ`"): let `M_c` be a proper trait
model over the generic base `(F, X_c, ι)` with proper `X_c`, `X_c'` and full generic fibre, `V`
an open of its total space with quasi-compact inclusion which embeds into an affine space over
the trait (an immersion `c_V : V ⟶ 𝔸(ι_V; S)` over `S`), and `b : V ⟶ 𝔸¹_S` a coordinate. Then
the twist equation (`NearbyCyclesModel.IsTraitModelOfGenericBase.TwistEquation`) holds for
`M_c|_V` and `b`: there are `u : c^* ω_{X_c} ≅ ω_{X₂} ⊗ T` and `v : p^* ω_{X'} ≅ ω_{𝒳''_s} ⊗ T`,
`T = ℚ̄_ℓ(0)[2]`, with `p^* θ_{M_c|_V} ≫ v = α ≫ Ψ_{M''}(u) ≫ κ ≫ θ_{M''} ▷ T`.

The twist equation of `M_c|_V` follows from that of its generic standard model `V ⟶ S` over
`(η, V_η, 𝟙)`
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_iso_map_θ_eq_twist_restrictOpen_of_traitFibreModel`),
which is quasi-projective over `S` through the standard chart `𝔸(ι_V; S) ⟶ ℙ(Option ι_V; S)`
(`NearbyCyclesModel.exists_twist_of_isImmersion`). -/
theorem exists_iso_map_θ_eq_twist_restrictOpen_of_immersion
    (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ)
    (hgen : IsPullback Mc.ε gc Xc.hom (traitGenericPointToSpec k' ≫ ι)) {ιV : Type u}
    [Finite ιV] (cV : (Mc.restrictOpen V).total ⟶ 𝔸(ιV; trait k')) [IsImmersion cV]
    (hcV : cV ≫ 𝔸(ιV; trait k') ↘ trait k' = V.ι ≫ qc) :
    (hMc.restrictOpen V).TwistEquation ℓ hb D DK := by
  have hR := (hMc.restrictOpen V).isTraitModelOver
  have := hR.locallyOfFiniteType
  have := hR.quasiCompact
  have := hR.isSeparated
  have hT := isTraitModelOfGenericBase_traitFibreModel (V.ι ≫ qc)
  have hTM := hT.isTraitModelOver
  have := hTM.locallyOfFiniteType_genericSliceBase (traitSliceCoord k') hb
  have := hTM.quasiCompact_genericSliceBase (traitSliceCoord k') hb
  have := hTM.isSeparated_genericSliceBase (traitSliceCoord k') hb
  have := hTM.locallyOfFiniteType_baseChangeSpecial_traitSlice (traitSliceCoord k') hb
  have := hTM.quasiCompact_baseChangeSpecial_traitSlice (traitSliceCoord k') hb
  have := hTM.isSeparated_baseChangeSpecial_traitSlice (traitSliceCoord k') hb
  -- the generic standard model of `V` is quasi-projective over the trait
  classical
  have hn : Nat.card (Option ιV) = Nat.card ιV + 1 := by
    have := Fintype.ofFinite ιV
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_option]
  have he : (cV ≫ AffineSpace.toRelativeProjectiveSpace ιV (trait k')) ≫
      ℙ(Option ιV; trait k') ↘ trait k' = V.ι ≫ qc := by
    rw [Category.assoc, AffineSpace.toRelativeProjectiveSpace_over, hcV]
  exact exists_iso_map_θ_eq_twist_restrictOpen_of_traitFibreModel ℓ hMc V hb D DK hgen
    (exists_twist_of_isImmersion hb D DK hT (exists_isIso_genericFibre_traitFibreModel _) hn
      (cV ≫ AffineSpace.toRelativeProjectiveSpace ιV (trait k')) he)

end IsTraitModelOfGenericBase

end NearbyCyclesModel

end ProEtale.CondensedRing

end AlgebraicGeometry
