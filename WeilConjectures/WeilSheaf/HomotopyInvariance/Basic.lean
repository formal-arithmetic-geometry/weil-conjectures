/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.SmoothBaseChange

/-!
# Auxiliary facts for homotopy invariance of Weil complexes

Facts used in the dévissage proving homotopy invariance along trivial line bundles
(`WeilConjectures.WeilSheaf.HomotopyInvariance`):

- Weil complexes on an empty scheme vanish (`AlgebraicGeometry.WeilComplex.isZero_of_isEmpty`);
- the trivial line bundle `X ×_{k₀} 𝔸¹ ⟶ X` is smooth
  (`AlgebraicGeometry.WeilComplex.smooth_of_isPullback`);
- a Weil complex on a reduced scheme has lisse cohomology sheaves on a dense open subscheme
  (`AlgebraicGeometry.WeilComplex.exists_dense_isLisse_homologySheaf_upperStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- Every Weil complex on an empty scheme is zero. -/
lemma isZero_of_isEmpty {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [IsEmpty X]
    (K : WeilComplex k₀ l X) : IsZero K :=
  sorry

/-- A trivial line bundle `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` is smooth, as a base change of the smooth
morphism `𝔸¹ ⟶ Spec k₀`. -/
lemma smooth_of_isPullback {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] {π : Y ⟶ X}
    {s : Y ⟶ affineLine k₀}
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀))) : Smooth π :=
  sorry

/-- **Generic lissity for Weil complexes.** A Weil complex on a reduced `k₀`-scheme of finite type
has lisse cohomology sheaves on a dense open subscheme: it has finitely many nonzero cohomology
sheaves, each lisse on a dense open subscheme
(`AlgebraicGeometry.WeilSheaf.exists_dense_isLisse_upperStar`), and the pullback commutes with
the cohomology sheaves. -/
lemma exists_dense_isLisse_homologySheaf_upperStar {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IsReduced X] (K : WeilComplex k₀ l X) :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      ∀ n : ℤ, ((homologySheaf n).obj ((upperStar U.ι).obj K)).IsLisse :=
  sorry

/-- If `X` is empty, the unit `K ⟶ Rφ_* φ^* K` is an isomorphism for every `φ : Y ⟶ X`, both
sides being zero. -/
lemma isIso_unit_app_of_isEmpty {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IsEmpty X] (K : WeilComplex k₀ l X) :
    IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) φ).unit.app K) :=
  sorry

end AlgebraicGeometry.WeilComplex
