/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.HomotopyInvariance
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.LowerShriek

/-!
# Weil complexes on the trivial line bundle

Let `π : Y ⟶ X` be the trivial line bundle `Y ≅ X ×_{k₀} 𝔸¹` over a `k₀`-scheme `X`, given by a
cartesian square `Y ⟶ 𝔸¹, Y ⟶ X` over `Spec k₀`. This file records the two inputs on `π` from
other chapters that the rank-one Thom isomorphism `Rπ₀! π^* P ≅ P(-1)[-2]`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_upperStar_comp_derivedLowerShriek_of_isPullback`,
blueprint `thm-pur-rank-one-thom`) is deduced from:

- the affine-line adjunction `Rπ₀! ⊣ π^*(1)[2]`
  (`AlgebraicGeometry.WeilComplex.nonempty_adjunction_derivedLowerShriek_of_isPullback`,
  blueprint `cor-amb-affine-space-adjunction` for `d = 1`);
- homotopy invariance: the unit `K ⟶ Rπ_* π^* K` of `π^* ⊣ Rπ_*` is an isomorphism
  (`AlgebraicGeometry.WeilComplex.isIso_upperStarDerivedLowerStarAdjunction_unit_app_of_isPullback`,
  blueprint `lem-pur-a1-direct-image`, extended from `Λ_X` to all Weil complexes).

The affine-line adjunction is proved on the étale side with finite coefficients
(`AlgebraicGeometry.Etale.nonempty_adjunction_affineLine`); its passage to `ℓ`-adic Weil complexes
is not formalized, so it is stated here with `sorry`. Homotopy invariance is deduced from the case
of Weil complexes with lisse cohomology
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_of_isLisse_homologySheaf`) by passing to the
reduced subscheme and Noetherian induction
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_of_isClosedImmersion_of_isReduced`).

From them, `π^* ⋙ Rπ₀!` is left adjoint to `(1)[2] ⋙ π^* ⋙ Rπ_* ≅ (1)[2]`, whose left adjoint is
also the inverse autoequivalence `(-1)[-2]`; uniqueness of left adjoints gives the Thom
isomorphism (`AlgebraicGeometry.WeilComplex.upperStarCompDerivedLowerShriekIsoOfAdjunction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Twist

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

variable (k₀ l X) in
/-- For `m + n = 0` and `a + b = 0`, the twist-shift `K ↦ K(m)[a]` followed by `K ↦ K(n)[b]` is the
identity. -/
noncomputable def tateTwistShiftCompTateTwistShiftIso (m n a b : ℤ) (hmn : m + n = 0)
    (hab : a + b = 0) :
    (tateTwist k₀ l X m ⋙ shiftFunctor (WeilComplex k₀ l X) a) ⋙
        (tateTwist k₀ l X n ⋙ shiftFunctor (WeilComplex k₀ l X) b) ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft (tateTwist k₀ l X m)
      (Functor.isoWhiskerRight ((tateTwist k₀ l X n).commShiftIso a)
        (shiftFunctor (WeilComplex k₀ l X) b)) ≪≫
    Functor.isoWhiskerLeft (tateTwist k₀ l X m ⋙ tateTwist k₀ l X n)
      (shiftFunctorCompIsoId (WeilComplex k₀ l X) a b hab) ≪≫
    Functor.rightUnitor _ ≪≫ tateTwistCompTateTwistIso m n hmn

variable (k₀ l X) in
/-- The twist-shift `K ↦ K(-1)[-2]` is left adjoint to `K ↦ K(1)[2]`: they are inverse
autoequivalences of the Weil complexes. -/
noncomputable def tateTwistShiftAdjunction :
    tateTwist k₀ l X (-1) ⋙ shiftFunctor (WeilComplex k₀ l X) (-2 : ℤ) ⊣
      tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ) :=
  (CategoryTheory.Equivalence.mk
    (tateTwist k₀ l X (-1) ⋙ shiftFunctor (WeilComplex k₀ l X) (-2 : ℤ))
    (tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ))
    (tateTwistShiftCompTateTwistShiftIso k₀ l X (-1) 1 (-2) 2 (by norm_num)
      (by norm_num)).symm
    (tateTwistShiftCompTateTwistShiftIso k₀ l X 1 (-1) 2 (-2) (by norm_num)
      (by norm_num))).toAdjunction

end Twist

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

include hπ in
/-- Blueprint `cor-amb-affine-space-adjunction` (for `d = 1`, on Weil complexes): **the
affine-line adjunction**. For the trivial line bundle `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X`, given by a
cartesian square `Y ⟶ 𝔸¹, Y ⟶ X` over `Spec k₀`, the direct image with compact support `Rπ₀!`
of Weil complexes is left adjoint to `P ↦ π^*(P(1)[2])`.

This is the `ℓ`-adic Weil form of the finite-coefficient étale adjunction
`AlgebraicGeometry.Etale.nonempty_adjunction_affineLine` (`Rp_! ⊣ Lp^*(1)[2]` for
`p : 𝔸¹_S ⟶ S`), which is proved from the projective-line adjunction `thm-amb-p1-adjunction`.
Its passage to `ℓ`-adic Weil complexes (limits over the finite coefficients, rationalization
and compatibility with the Frobenius structures) belongs to the chapter on the exceptional
inverse image and is not formalized; it is stated here with `sorry`. -/
theorem nonempty_adjunction_derivedLowerShriek_of_isPullback :
    Nonempty (derivedLowerShriek k₀ l π ⊣
      (tateTwist k₀ l X 1 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 : ℤ)) ⋙ upperStar π) :=
  sorry

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
      Functor.rightUnitor _)).leftAdjointUniq (tateTwistShiftAdjunction k₀ l X)

end TrivialLineBundle

end AlgebraicGeometry.WeilComplex
