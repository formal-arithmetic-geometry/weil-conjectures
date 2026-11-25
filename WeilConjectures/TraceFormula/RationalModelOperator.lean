/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatiblePaste
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralUpperShriekCompatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriek
public import WeilConjectures.TraceFormula.IntegersToPadicAlgClLowerShriek
public import WeilConjectures.TraceFormula.IntegralCompactPullback
public import WeilConjectures.TraceFormula.RationalCompactPullback
public import WeilConjectures.TraceFormula.RationalModel

/-!
# The operators of rational Frobenius correspondences and of their integral models

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`. For a proper
endomorphism `Φ` of `X` and a Frobenius correspondence `ψ : LΦ^* K ⟶ K` with coefficients `E`
(resp. `𝒪_E`), the operator `T_{c_m}(ψ_m) = RΓ_c(X, ψ_m) ∘ Φ_m^♯` on `RΓ_c(X, K)` is defined as
for `ℚ̄_ℓ` (`ProEtale.CondensedRing.frobeniusCompactOperator`), with the pullback `Φ_m^♯` on
compactly supported cohomology induced by the unit of `LΦ_m^* ⊣ RΦ_{m*}` and `RΦ_{m!} ≅ RΦ_{m*}`
(`ProEtale.CondensedRing.ContinuousMapRingObj.compactPullback`,
`ProEtale.CondensedRing.PadicIntegersRingObj.compactPullback`).

For an integral model `(K₀, θ)` of `(K, ψ)` with `ℓ^N ψ = θ ⊗ E`
(`ProEtale.CondensedRing.exists_integralModel_frobeniusCorrespondence`), the operators satisfy
`ℓ^{N m} T_{c_m}(ψ_m) = T_{c_m}(θ_m) ⊗ E`
(`ProEtale.CondensedRing.pow_smul_frobeniusCompactOperator_eq`). As in
`WeilConjectures.TraceFormula.RationalModel`, the denominator is a power of `ℓ` rather than of
`π_E`, which is equivalent.

## Implementation details

The proof combines the identity `ℓ^{N m} ψ_m = θ_m ⊗ E` for the iterates
(`ProEtale.CondensedRing.pow_smul_frobeniusCoefficientIterate_eq`, read through the canonical
comparisons by `ProEtale.CondensedRing.extendScalarsUpperStarIterateIso_eq`) with the
compatibility of the pullbacks `h^♯` with the extension of scalars
(`ProEtale.CondensedRing.squareCompatible_compactPullback`), which follows from the
compatibility of the unit of `Lh^* ⊣ Rh_*`, of `Rh_! ≅ Rh_*` and of the composition
isomorphisms of the lower shrieks with the extension of scalars.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory MonObj

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : FiniteIntermediateField ℓ)
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

-- The coefficient ring `𝒪_E`.
set_option quotPrecheck false in
local notation "𝒪" => Profinite.padicIntegersRingObj ℓ E.1

-- The coefficient ring `E`.
set_option quotPrecheck false in
local notation "𝔼" => Profinite.continuousMapRingObj E.1

variable {K : BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X.left)}
  {K₀ : BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left)}

/-! ### Compatibility with the extension of scalars `𝒪_E ⟶ E` -/

/-- `Rh_! ≅ Rh_*` for a proper `h` is compatible with the extension of scalars `𝒪_E ⟶ E`, read
on the comparisons of the coefficient change
(`squareCompatible_lowerShriekIsoLowerStar_extendScalars` in the form used by
`squareCompatible_compactPullback`). -/
private lemma squareCompatible_lowerShriekIsoLowerStar_shriekOfCompactification (h : Y ⟶ X)
    [IsProper h.left] :
    NatTrans.SquareCompatible
      ((extendScalarsCoefficientChange ℓ E k).shriekOfCompactification
        (compactificationOverField h))
      ((extendScalarsCoefficientChange ℓ E k).push h)
      (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E.1 h).hom
      (ContinuousMapRingObj.boundedConstructibleLowerShriekIsoLowerStar ℓ E h).hom := by
  rw [ContinuousMapRingObj.boundedConstructibleLowerShriekIsoLowerStar_eq_pushforwardData ℓ k E]
  exact (squareCompatible_lowerShriekIsoLowerStar_extendScalars ℓ E k h).of_eq
    (boundedConstructibleLowerShriekExtendScalarsIso_eq_shriekOfCompactification ℓ E k h) rfl

/-- The composition isomorphisms of `Rf_!` are compatible with the extension of scalars
`𝒪_E ⟶ E`, read on the comparisons of the coefficient change
(`squareCompatible_lowerShriekComp_extendScalars` in the form used by
`squareCompatible_compactPullback`). -/
private lemma squareCompatible_lowerShriekComp_shriekOfCompactification {S : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom] (f : X ⟶ Y)
    (g : Y ⟶ S) :
    NatTrans.SquareCompatible
      ((extendScalarsCoefficientChange ℓ E k).shriekOfCompactification
        (compactificationOverField (f ≫ g)))
      (Functor.pasteSquareIso
        ((extendScalarsCoefficientChange ℓ E k).shriekOfCompactification
          (compactificationOverField f))
        ((extendScalarsCoefficientChange ℓ E k).shriekOfCompactification
          (compactificationOverField g)))
      (boundedConstructibleLowerShriekComp_padicIntegers ℓ E.1 f g).hom
      (boundedConstructibleLowerShriekComp ℓ E f g).hom := by
  have hc := (squareCompatible_lowerShriekComp_extendScalars ℓ E k f g).of_eq
    (boundedConstructibleLowerShriekExtendScalarsIso_eq_shriekOfCompactification ℓ E k _)
    (congrArg₂ Functor.pasteSquareIso
      (boundedConstructibleLowerShriekExtendScalarsIso_eq_shriekOfCompactification ℓ E k f)
      (boundedConstructibleLowerShriekExtendScalarsIso_eq_shriekOfCompactification ℓ E k g))
  rwa [← boundedConstructibleLowerShriekComp_eq_pushforwardData] at hc

/-- The pullbacks `h^♯ : RΓ_c(X, -) ⟶ RΓ_c(Y, Lh^* -)` on compactly supported cohomology of
`𝒪̲_E` and `E̲` for a proper `h` are compatible with the extension of scalars. -/
theorem squareCompatible_compactPullback (h : Y ⟶ X) [IsProper h.left] :
    NatTrans.SquareCompatible
      ((extendScalarsCoefficientChange ℓ E k).shriekOfCompactification
        (compactificationOverField (toPoint X)))
      (Functor.pasteSquareIso (boundedConstructibleUpperStarExtendScalarsIso ℓ E h)
        ((extendScalarsCoefficientChange ℓ E k).shriekOfCompactification
          (compactificationOverField (toPoint Y))))
      (PadicIntegersRingObj.compactPullback ℓ E.1 h)
      (ContinuousMapRingObj.compactPullback ℓ E h) := by
  have hι := squareCompatible_lowerShriekIsoLowerStar_shriekOfCompactification ℓ E (k := k) h
  have hc := squareCompatible_lowerShriekComp_shriekOfCompactification ℓ E (k := k) h (toPoint X)
  unfold PadicIntegersRingObj.compactPullback ContinuousMapRingObj.compactPullback
  simp only [PadicIntegersRingObj.boundedConstructibleLowerShriekCompToPoint, Iso.trans_hom,
    Iso.symm_hom, eqToIso.hom]
  exact (NatTrans.SquareCompatible.leftUnitor_inv _).comp
    ((NatTrans.SquareCompatible.whiskerRight _ (NatTrans.SquareCompatible.unit
      ((extendScalarsCoefficientChange ℓ E k).isMateSquare_pull_push h))).comp
    ((NatTrans.SquareCompatible.associator_hom _ _ _).comp
    ((NatTrans.SquareCompatible.whiskerLeft _ (NatTrans.SquareCompatible.whiskerRight _
      hι.inv)).comp
    (NatTrans.SquareCompatible.whiskerLeft _
      (hc.inv.comp
        ((extendScalarsCoefficientChange ℓ E k).squareCompatible_shriekOfCompactification_eqToHom
          (comp_toPoint h) _ _))))))

/-- The comparison `LΦ_m^* ⋙ (-)_E ≅ (-)_E ⋙ LΦ_m^*` assembled from the canonical comparison for
`Φ` is the canonical comparison for `Φ_m`. -/
lemma extendScalarsUpperStarIterateIso_eq (Φ : X ⟶ X) (m : ℕ) :
    extendScalarsUpperStarIterateIso ℓ E Φ (boundedConstructibleUpperStarExtendScalarsIso ℓ E Φ) m =
      boundedConstructibleUpperStarExtendScalarsIso ℓ E (frobeniusIterate Φ m) := by
  induction m with
  | zero =>
    have hc : NatTrans.SquareCompatible
        (boundedConstructibleUpperStarExtendScalarsIso ℓ E (frobeniusIterate Φ 0))
        (Functor.idSquareIso (boundedConstructibleExtendScalars X.left ℓ E))
        (upperStarIterateZeroIso ℓ 𝒪 Φ).hom (upperStarIterateZeroIso ℓ 𝔼 Φ).hom := by
      simpa only [upperStarIterateZeroIso, Iso.trans_hom, eqToIso.hom] using
        (BoundedConstructibleCoefficientChange.squareCompatible_eqToHom
          (fun f ↦ boundedConstructibleUpperStarExtendScalarsIso ℓ E f)
          (frobeniusIterate_zero Φ) (by rw [frobeniusIterate_zero])
          (by rw [frobeniusIterate_zero])).comp
        ((extendScalarsCoefficientChange ℓ E k).squareCompatible_upperStarId X)
    refine Iso.ext (NatTrans.ext (funext fun K₀ ↦ ?_))
    rw [← cancel_mono ((upperStarIterateZeroIso ℓ 𝔼 Φ).hom.app _)]
    simpa [extendScalarsUpperStarIterateIso, extendScalarsUpperStarIterateZeroIso] using hc K₀
  | succ m ih =>
    have hc : NatTrans.SquareCompatible
        (boundedConstructibleUpperStarExtendScalarsIso ℓ E (frobeniusIterate Φ (m + 1)))
        (Functor.pasteSquareIso
          (boundedConstructibleUpperStarExtendScalarsIso ℓ E (frobeniusIterate Φ m))
          (boundedConstructibleUpperStarExtendScalarsIso ℓ E Φ))
        (upperStarIterateSuccIso ℓ 𝒪 Φ m).hom (upperStarIterateSuccIso ℓ 𝔼 Φ m).hom := by
      simpa only [upperStarIterateSuccIso, Iso.trans_hom, eqToIso.hom] using
        (BoundedConstructibleCoefficientChange.squareCompatible_eqToHom
          (fun f ↦ boundedConstructibleUpperStarExtendScalarsIso ℓ E f)
          (frobeniusIterate_succ Φ m) (by rw [frobeniusIterate_succ])
          (by rw [frobeniusIterate_succ])).comp
        ((extendScalarsCoefficientChange ℓ E k).pull_comp Φ (frobeniusIterate Φ m))
    refine Iso.ext (NatTrans.ext (funext fun K₀ ↦ ?_))
    rw [← cancel_mono ((upperStarIterateSuccIso ℓ 𝔼 Φ m).hom.app _)]
    simpa [extendScalarsUpperStarIterateIso, extendScalarsUpperStarIterateSuccIso, ih] using
      hc K₀

/-- If `ℓ^N ψ = θ ⊗ E` for a Frobenius correspondence `ψ : LΦ^* K ⟶ K` with `E`-coefficients and
an integral model `θ : LΦ^* K₀ ⟶ K₀`, read through `e : (K₀)_E ≅ K` and the canonical comparison
`LΦ^* ⋙ (-)_E ≅ (-)_E ⋙ LΦ^*` (as produced by `exists_integralModel_frobeniusCorrespondence`),
then for every `m` the operators of the iterates satisfy
```
ℓ^{N m} T_{c_m}(ψ_m) = T_{c_m}(θ_m) ⊗ E,
```
read through `RΓ_c(X, e)` and the compatibility `RΓ_c(X, -) ⋙ (-)_E ≅ (-)_E ⋙ RΓ_c(X, -)`
(`boundedConstructibleLowerShriekExtendScalarsIso`). -/
theorem pow_smul_frobeniusCompactOperator_eq {Φ : X ⟶ X} [IsProper Φ.left]
    (e : (boundedConstructibleExtendScalars X.left ℓ E).obj K₀ ≅ K) {N : ℕ}
    {ψ : (boundedConstructibleUpperStar 𝔼 ℓ Φ).obj K ⟶ K}
    {θ : (boundedConstructibleUpperStar 𝒪 ℓ Φ).obj K₀ ⟶ K₀}
    (h : ((ℓ : ℤ) ^ N) • ψ =
      (boundedConstructibleUpperStar 𝔼 ℓ Φ).map e.inv ≫
        (boundedConstructibleUpperStarExtendScalarsIso ℓ E Φ).inv.app K₀ ≫
        (boundedConstructibleExtendScalars X.left ℓ E).map θ ≫ e.hom)
    (m : ℕ) :
    ((ℓ : ℤ) ^ (N * m)) • ContinuousMapRingObj.frobeniusCompactOperator (E := E) ψ m =
      (ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E (toPoint X)).map e.inv ≫
        (boundedConstructibleLowerShriekExtendScalarsIso ℓ E (toPoint X)).inv.app K₀ ≫
        (boundedConstructibleExtendScalars _ ℓ E).map
          (PadicIntegersRingObj.frobeniusCompactOperator ℓ E.1 θ m) ≫
        (boundedConstructibleLowerShriekExtendScalarsIso ℓ E (toPoint X)).hom.app K₀ ≫
        (ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E (toPoint X)).map e.hom := by
  have hi := pow_smul_frobeniusCoefficientIterate_eq ℓ E Φ
    (boundedConstructibleUpperStarExtendScalarsIso ℓ E Φ) e h m
  simp only [extendScalarsUpperStarIterateIso_eq ℓ E Φ m] at hi
  simp only [boundedConstructibleLowerShriekExtendScalarsIso_eq_shriekOfCompactification ℓ E k]
  have hc := (squareCompatible_compactPullback ℓ E (k := k)
    (frobeniusIterate Φ m)).inv_app_comp_pasteSquareIso K₀
  simp only [padicIntegersPushforwardData_lowerShriekOfCompactification,
    continuousMapPushforwardData_lowerShriekOfCompactification] at hc
  have n₁ := ((extendScalarsCoefficientChange ℓ E k).shriekOfCompactification
    (compactificationOverField (toPoint X))).hom.naturality (frobeniusCoefficientIterate θ m)
  have n₂ := (ContinuousMapRingObj.compactPullback ℓ E (frobeniusIterate Φ m)).naturality e.inv
  simp only [Functor.comp_map, padicIntegersPushforwardData_lowerShriekOfCompactification,
    continuousMapPushforwardData_lowerShriekOfCompactification] at n₁ n₂
  simp only [ContinuousMapRingObj.frobeniusCompactOperator,
    PadicIntegersRingObj.frobeniusCompactOperator]
  simp only [← Preadditive.comp_zsmul, ← Functor.map_zsmul]
  simp only [hi]
  simp only [Functor.map_comp, assoc, reassoc_of% n₁, reassoc_of% hc, reassoc_of% n₂]

end AlgebraicGeometry.ProEtale.CondensedRing
