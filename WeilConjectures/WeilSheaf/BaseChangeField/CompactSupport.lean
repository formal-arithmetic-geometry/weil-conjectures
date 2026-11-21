/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.WeilSheaf.BaseChangeField.Cohomology
public import WeilConjectures.WeilSheaf.BaseChangeField.ExtensionByZero
public import WeilConjectures.WeilSheaf.BaseChangeField.Restriction
public import WeilConjectures.WeilSheaf.LowerShriekIndependence
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact

/-!
# Compactly supported cohomology under a finite extension of the base field

Let `k₀ ⊆ K` be finite fields with `[K : k₀] = m` and `X` a separated `k₀`-scheme of finite
type. A finite extension of the constant field does not change the geometric scheme
`X ⊗_{k₀} k̄`, nor a Weil sheaf on it, nor its cohomology; it replaces the geometric Frobenius of
`k₀` by its `m`-th power. So the restriction `F_K` of a Weil sheaf `F` on `X` to
`X_K = X ×_{k₀} K` (`AlgebraicGeometry.WeilSheaf.baseChangeField`) has
`H_c^r(X_K ⊗_K k̄, F_K) = H_c^r(X ⊗_{k₀} k̄, F)`, with the Frobenius of `K` acting as `Fᵐ`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_baseChangeField`.

## Implementation details

The direct image with compact support is computed on both sides by a compactification
`X ⟶ Z ⟶ Spec k₀` and its base change `X_K ⟶ Z_K ⟶ Spec K`
(`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_comp_ι_iso`); transport of Weil
sheaves along the identifications of geometric fibers commutes with the extension by zero
(`AlgebraicGeometry.ProEtaleWeilSheaf.transportExtensionByZeroIso`) and with the derived direct
image (`AlgebraicGeometry.ProEtaleWeilSheaf.transportRightDerivedLowerStarIso`).

The instances `IsSeparated` and `QuasiCompact` for the structure morphism of `X_K` are stated
here rather than next to `AlgebraicGeometry.Scheme.baseChangeField`, to keep that widely imported
file light.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  (K : Type u) [Field K] [Algebra k₀ K]

instance [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    IsSeparated (X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsSeparated)
    (IsPullback.of_hasPullback _ _) ‹_›

instance [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    QuasiCompact (X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact)
    (IsPullback.of_hasPullback _ _) ‹_›

namespace WeilSheaf

open ProEtaleWeilSheaf Scheme.Hom

variable [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {X}
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [Finite K] [Fact (ringChar K ≠ l)]

/-- **Compactly supported cohomology under a finite extension of the base field.** Let `K` be a
finite extension of `k₀` of degree `m` and `F` a Weil sheaf on a separated `k₀`-scheme `X` of
finite type. The compactly supported cohomology `H_c^r(X_K ⊗_K k̄, F_K)` of the restriction
`F_K` of `F` to `X_K = X ×_{k₀} K` is `H_c^r(X ⊗_{k₀} k̄, F)`, with the geometric Frobenius of
`K` acting as the `m`-th power of that of `k₀`. -/
theorem nonempty_equiv_compactlySupportedCohomology_baseChangeField (F : WeilSheaf k₀ l X)
    (r : ℤ) :
    Nonempty ((((baseChangeField K).obj F).compactlySupportedCohomology r).Equiv
      ((F.compactlySupportedCohomology r).powFrobenius (Module.finrank k₀ K))) := by
  set m := Module.finrank k₀ K
  have hm : Nat.card K = Nat.card k₀ ^ m := Module.natCard_eq_pow_finrank
  -- a compactification `X ⟶ Z ⟶ Spec k₀` and its base change `X_K ⟶ Z_K ⟶ Spec K`
  obtain ⟨Z, g, i, hgi, _, _⟩ := HasCompactification.compactification
    (X ↘ Spec (CommRingCat.of k₀)) (hf := hasCompactification_of_over (k₀ := k₀) _)
  let : Z.Over (Spec (CommRingCat.of k₀)) := ⟨g⟩
  have : g.IsOver (Spec (CommRingCat.of k₀)) := ⟨Category.comp_id g⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨hgi.symm⟩
  let iK : X.baseChangeField k₀ K ⟶ Z.baseChangeField k₀ K :=
    pullback.map _ _ _ _ i (𝟙 _) (𝟙 _) (by rw [Category.comp_id, comp_over]) (by simp)
  have hiK : iK ≫ Z.baseChangeField k₀ K ↘ Spec (CommRingCat.of K) =
      X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K) :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have : iK.IsOver (Spec (CommRingCat.of K)) := ⟨hiK⟩
  let gK := Z.baseChangeField k₀ K ↘ Spec (CommRingCat.of K)
  have : IsProper gK := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback _ _) (inferInstanceAs (IsProper g))
  have : gK.IsOver (Spec (CommRingCat.of K)) := ⟨Category.comp_id _⟩
  obtain ⟨eK⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_ι_iso (k₀ := K) (l := l) iK gK
    hiK.symm
  obtain ⟨e₀⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_ι_iso (k₀ := k₀) (l := l) i g hgi
  -- the identifications of the geometric fibers
  have hS : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap k₀ K)))
      (Spec (CommRingCat.of K) ↘ Spec (CommRingCat.of K))
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) :=
    IsPullback.id_vert _
  let θ := geometricFiberBaseChangeIso (isPullback_baseChangeField (k₀ := k₀) X K)
  let θZ := geometricFiberBaseChangeIso (isPullback_baseChangeField (k₀ := k₀) Z K)
  let θS := geometricFiberBaseChangeIso hS
  have hθ := geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius
    (isPullback_baseChangeField (k₀ := k₀) X K) m hm
  have hθZ := geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius
    (isPullback_baseChangeField (k₀ := k₀) Z K) m hm
  have hθS := geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius hS m hm
  have hsqi := geometricFiberBaseChangeIso_hom_comp_geometricFiberMap
    (isPullback_baseChangeField (k₀ := k₀) X K) (isPullback_baseChangeField (k₀ := k₀) Z K)
    (φ := i) (comp_over i _) (φ' := iK) (comp_over iK _) (pullback.lift_fst _ _ _)
  have hsqg := geometricFiberBaseChangeIso_hom_comp_geometricFiberMap
    (isPullback_baseChangeField (k₀ := k₀) Z K) hS (φ := g) (Category.comp_id _) (φ' := gK)
    (Category.comp_id _) pullback.condition.symm
  let T := ProEtaleWeilSheaf.transport (l := l) θ m hθ
  let TZ := ProEtaleWeilSheaf.transport (l := l) θZ m hθZ
  let TS := ProEtaleWeilSheaf.transport (l := l) θS m hθS
  -- `Rf_K! F_K ≅ T_S (Rf_! F)`
  let β : ((WeilComplex.derivedLowerShriek K l
      (X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K))).obj
        (toComplex.obj ((baseChangeField K).obj F))).obj ≅
      TS.mapDerivedCategory.obj ((WeilComplex.derivedLowerShriek k₀ l
        (X ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj F)).obj :=
    eK.app _ ≪≫ (ProEtaleWeilSheaf.lowerStar K l gK).rightDerivedFunctor.mapIso
      ((ProEtaleWeilSheaf.extensionByZero K l iK).mapDerivedCategory.mapIso
          ((T.mapDerivedCategorySingleFunctor 0).symm.app F.obj) ≪≫
        (Functor.mapDerivedCategoryCompIso T _).app _ ≪≫
        (Functor.mapDerivedCategoryNatIso
          (transportExtensionByZeroIso θ m hθ θZ hθZ i iK hsqi)).app _ ≪≫
        (Functor.mapDerivedCategoryCompIso _ TZ).symm.app _) ≪≫
      (transportRightDerivedLowerStarIso θZ m hθZ θS hθS g gK hsqg).app _ ≪≫
      TS.mapDerivedCategory.mapIso (e₀.app (toComplex.obj F)).symm
  let α : ((WeilComplex.homologySheaf r).obj ((WeilComplex.derivedLowerShriek K l
      (X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K))).obj
        (toComplex.obj ((baseChangeField K).obj F)))).obj ≅
      TS.obj ((WeilComplex.homologySheaf r).obj ((WeilComplex.derivedLowerShriek k₀ l
        (X ↘ Spec (CommRingCat.of k₀))).obj (toComplex.obj F))).obj :=
    (DerivedCategory.homologyFunctor _ r).mapIso β ≪≫
      (TS.mapDerivedCategoryHomologyFunctorIso r).symm.app _
  obtain ⟨e, he⟩ := exists_linearEquiv_globalSections_of_iso_transport θS m hθS _ _ α
  exact ⟨⟨e, fun x ↦ (he x).trans
    (LinearMap.congr_fun (FrobeniusModule.powFrobenius_frobeniusEnd _ m).symm (e x))⟩⟩

end WeilSheaf

end AlgebraicGeometry
