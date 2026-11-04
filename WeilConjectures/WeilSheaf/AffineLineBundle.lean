/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
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
  (`AlgebraicGeometry.WeilComplex.isIso_upperStarDerivedLowerStarAdjunction_unit_app_of_isPullback`,
  stated here with `sorry`).

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
/-- For `m + n = 0` and `a + b = 0`, the twist-shifts `K ↦ K(m)[a]` and `K ↦ K(n)[b]` are inverse
autoequivalences of the Weil complexes. -/
noncomputable def tateTwistShiftEquiv (m n a b : ℤ) (hmn : m + n = 0) (hab : a + b = 0) :
    WeilComplex k₀ l X ≌ WeilComplex k₀ l X :=
  CategoryTheory.Equivalence.mk
    (tateTwist k₀ l X m ⋙ shiftFunctor (WeilComplex k₀ l X) a)
    (tateTwist k₀ l X n ⋙ shiftFunctor (WeilComplex k₀ l X) b)
    (tateTwistShiftCompTateTwistShiftIso k₀ l X m n a b hmn hab).symm
    (tateTwistShiftCompTateTwistShiftIso k₀ l X n m b a (by omega) (by omega))

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

omit [Finite k₀] [Y.Over (Spec (CommRingCat.of k₀))] [π.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] in
include hπ in
/-- The trivial line bundle `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` is smooth of relative dimension one, as a
base change of `𝔸¹ ⟶ Spec k₀`. -/
theorem smoothOfRelativeDimension_one_of_isPullback : SmoothOfRelativeDimension 1 π := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hπ.flip this

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
/-- **Homotopy invariance for Weil complexes.** For the trivial line bundle
`π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X`, given by a cartesian square `Y ⟶ 𝔸¹, Y ⟶ X` over `Spec k₀`, the
unit `K ⟶ Rπ_* π^* K` of the adjunction `π^* ⊣ Rπ_*` of Weil complexes is an isomorphism for
every Weil complex `K` on `X`; that is, `π^*` is fully faithful.

For the constant coefficients `Λ_X` this is blueprint `lem-pur-a1-direct-image`, proved on the
étale side with finite coefficients as
`AlgebraicGeometry.Etale.isIso_unit_constantComplex_affineLine`. The statement for all Weil
complexes is not a blueprint node. Its proof needs the `ℓ`-adic form of the constant case and,
to pass from `Λ_X` to all `K`, smooth base change and a projection formula for `Rπ_*` on Weil
complexes; none of these is formalized, so it is left with `sorry`. -/
theorem isIso_upperStarDerivedLowerStarAdjunction_unit_app_of_isPullback
    (K : WeilComplex k₀ l X) :
    IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit.app K) :=
  sorry

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
