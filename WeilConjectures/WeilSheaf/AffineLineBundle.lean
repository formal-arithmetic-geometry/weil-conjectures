/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.LineSmooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.HomotopyInvariance
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.VerdierDual

/-!
# Weil complexes on the trivial line bundle

Let `π : Y ⟶ X` be the trivial line bundle `Y ≅ X ×_{k₀} 𝔸¹` over a `k₀`-scheme `X`, given by a
cartesian square `Y ⟶ 𝔸¹, Y ⟶ X` over `Spec k₀`. This file records the two inputs on `π` that
the rank-one Thom isomorphism `Rπ₀! π^* P ≅ P(-1)[-2]`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_upperStar_comp_derivedLowerShriek_of_isPullback`,
blueprint `thm-pur-rank-one-thom`) is deduced from:

- the affine-line adjunction `Rπ₀! ⊣ π^*(1)[2]`
  (`AlgebraicGeometry.WeilComplex.nonempty_adjunction_derivedLowerShriek_of_isPullback`), the
  adjunction `Rπ₀! ⊣ Rπ^!` transported along smooth purity `Rπ^! ≅ π^*(1)[2]` for Weil complexes
  (`AlgebraicGeometry.WeilComplex.nonempty_upperShriek_iso_of_smoothOfRelativeDimension`);
- homotopy invariance: the unit `K ⟶ Rπ_* π^* K` of `π^* ⊣ Rπ_*` is an isomorphism
  (`WeilComplex.isIso_upperStarDerivedLowerStarAdjunction_unit_app_of_isPullback`).

From them, `π^* ⋙ Rπ₀!` is left adjoint to `(1)[2] ⋙ π^* ⋙ Rπ_* ≅ (1)[2]`, whose left adjoint is
also the inverse autoequivalence `(-1)[-2]`; uniqueness of left adjoints gives the Thom
isomorphism (`AlgebraicGeometry.WeilComplex.upperStarCompDerivedLowerShriekIsoOfAdjunction`).
This argument does not produce the canonical map `τ_E = Rπ_! thom(E)` of the blueprint, only
some natural isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section TrivialLineBundle

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (π : Y ⟶ X) (s : Y ⟶ affineLine k₀)
  [π.IsOver (Spec (CommRingCat.of k₀))]
  (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
  [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

omit [Finite k₀] [Y.Over (Spec (CommRingCat.of k₀))] [π.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] in
include hπ in
/-- The trivial line bundle `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` is smooth of relative dimension one, as a
base change of `𝔸¹ ⟶ Spec k₀`. -/
theorem smoothOfRelativeDimension_one_of_isPullback : SmoothOfRelativeDimension 1 π :=
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hπ.flip inferInstance

include hπ in
/-- **The affine-line adjunction for Weil complexes** (the Weil form of
`cor-amb-affine-space-adjunction` for `d = 1`). For the trivial line bundle
`π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X`, given by a cartesian square `Y ⟶ 𝔸¹, Y ⟶ X` over `Spec k₀`, the
direct image with compact support `Rπ₀!` of Weil complexes is left adjoint to `P ↦ π^*(P(1)[2])`:
this is the adjunction `Rπ₀! ⊣ Rπ^!` transported along smooth purity `Rπ^! ≅ π^*(1)[2]`
(`AlgebraicGeometry.WeilComplex.nonempty_upperShriek_iso_of_smoothOfRelativeDimension`). -/
theorem nonempty_adjunction_derivedLowerShriek_of_isPullback :
    Nonempty (derivedLowerShriek k₀ l π ⊣
      (tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ)) ⋙ upperStar π) := by
  have := smoothOfRelativeDimension_one_of_isPullback π s hπ
  have : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over π]
    infer_instance
  have : QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over π]
    infer_instance
  have : HasUpperShriek k₀ l π := isLeftAdjoint_derivedLowerShriek π
  obtain ⟨e⟩ := nonempty_upperShriek_iso_of_smoothOfRelativeDimension (k₀ := k₀) (l := l) π 1
  exact ⟨(derivedLowerShriekUpperShriekAdjunction π).ofNatIsoRight (by simpa using e)⟩

include hπ in
/-- Blueprint `lem-pur-a1-direct-image` (for all Weil complexes): **homotopy invariance**. For
the trivial line bundle `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X`, given by a cartesian square
`Y ⟶ 𝔸¹, Y ⟶ X` over `Spec k₀`, the unit `K ⟶ Rπ_* π^* K` of the adjunction `π^* ⊣ Rπ_*` of
Weil complexes is an isomorphism for every Weil complex `K` on `X`; that is, `π^*` is fully
faithful.

For `K = Λ_X` with finite étale coefficients over an algebraically closed field this is
`AlgebraicGeometry.Etale.isIso_unit_constantComplex_affineLine`; for general `K` it follows from
the constant case by smooth base change (`sbc-thm-smooth-base-change`) and the acyclicity of
the affine line over strictly henselian bases. Here it is deduced from the case of a reduced
scheme (`AlgebraicGeometry.WeilComplex.isIso_unit_app_of_isClosedImmersion_of_isReduced`): `K` is
the direct image of its restriction to the reduced subscheme `X_red`, whose open complement is
empty, and smooth base change carries the unit along this direct image
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_derivedLowerStar_obj`). -/
theorem isIso_upperStarDerivedLowerStarAdjunction_unit_app_of_isPullback
    (K : WeilComplex k₀ l X) :
    IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit.app K) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of k₀))
  have : IsNoetherian X := ⟨⟩
  -- the reduced closed subscheme `r : X_red ⟶ X`, with empty open complement `j`
  let I := Scheme.IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds X)
  let r := I.subschemeι
  let : I.subscheme.Over (Spec (CommRingCat.of k₀)) := ⟨r ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : r.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : LocallyOfFiniteType (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (r ≫ X ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (r ≫ X ↘ Spec (CommRingCat.of k₀)))
  have : QuasiSeparated (I.subscheme ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiSeparated (r ≫ X ↘ Spec (CommRingCat.of k₀)))
  let j := (⊥ : X.Opens).ι
  have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.2⟩
  have hr : Set.range r = (⊤ : TopologicalSpace.Closeds X) := by simp [r, I]
  have hc : IsCompl (Set.range r.base) (Set.range j.base) := by
    rw [Set.range_eq_empty j.base]
    rw [show Set.range r.base = Set.univ by simpa using hr]
    exact isCompl_top_bot
  -- `K` is the direct image of its restriction to `X_red`
  obtain ⟨M, ⟨e⟩⟩ := derivedLowerStar_essImage_of_isZero r j hc K (isZero_of_isEmpty _)
  have := isIso_unit_app_derivedLowerStar_obj π s hπ r M
    fun Y' _ π' s' _ hπ' _ _ _ ↦ isIso_unit_app_of_isClosedImmersion_of_isReduced ⊤ I.subscheme r
      (Set.subset_univ _) Y' π' s' hπ' M
  exact (upperStarDerivedLowerStarAdjunction π).unit.isoLocus.prop_of_iso e this

/-- **The Thom isomorphism from the affine-line adjunction and homotopy invariance.** If `Rπ₀!` is
left adjoint to `P ↦ π^*(P(1)[2])` and the unit of `π^* ⊣ Rπ_*` is an isomorphism, then
`Rπ₀! π^* P ≅ P(-1)[-2]` naturally in `P`: `π^* ⋙ Rπ₀!` is left adjoint to
`(1)[2] ⋙ π^* ⋙ Rπ_* ≅ (1)[2]`, whose left adjoint is also `(-1)[-2]`. -/
noncomputable def upperStarCompDerivedLowerShriekIsoOfAdjunction
    (adj : derivedLowerShriek k₀ l π ⊣
      (tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ)) ⋙ upperStar π)
    [IsIso (upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit] :
    upperStar π ⋙ derivedLowerShriek k₀ l π ≅
      tateTwist k₀ l X (-1) ⋙ shiftFunctor (WeilComplex k₀ l X) (-2 : ℤ) :=
  (((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).comp adj).ofNatIsoRight
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (asIso (upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit).symm ≪≫
      Functor.rightUnitor _)).leftAdjointUniq
    (tateTwistShiftEquiv k₀ l X (-1) 1 (-2) 2 (by norm_num) (by norm_num)).toAdjunction

end TrivialLineBundle

end AlgebraicGeometry.WeilComplex
