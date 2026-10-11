/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Category

/-!
# Cohomology sheaves of shifted Weil complexes

The cohomology sheaves of a shifted Weil complex are those of the complex, reindexed:
`𝓗ⁿ(K[a]) ≅ 𝓗ⁿ⁺ᵃ(K)` (`AlgebraicGeometry.WeilComplex.homologySheafShiftIso`). In particular a
Weil sheaf `F` placed in degree `-a`, that is `F[a]`, has the single cohomology sheaf
`𝓗⁻ᵃ(F[a]) ≅ F`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The cohomology sheaves of a shifted Weil complex: `𝓗ⁿ(K[a]) ≅ 𝓗ⁿ'(K)` for `a + n = n'`,
those of the underlying complex of pro-étale Weil sheaves. -/
noncomputable def homologySheafShiftIso (K : WeilComplex k₀ l X) (a n n' : ℤ)
    (h : a + n = n') : (homologySheaf n).obj (K⟦a⟧) ≅ (homologySheaf n').obj K :=
  ObjectProperty.isoMk _ ((_root_.DerivedCategory.homologyFunctor _ n).mapIso
      (((WeilComplex.objectProperty k₀ l X).ι.commShiftIso a).app K) ≪≫
    ((_root_.DerivedCategory.homologyFunctor _ 0).shiftIso a n n' h).app K.obj)

/-- A shifted Weil sheaf `F[a]` has vanishing cohomology sheaves outside degree `-a`. -/
theorem isZero_homologySheaf_shift_toComplex (F : WeilSheaf k₀ l X) {a n : ℤ} (h : a + n ≠ 0) :
    IsZero ((homologySheaf n).obj ((WeilSheaf.toComplex.obj F)⟦a⟧)) :=
  (isZero_homologySheaf_singleComplex h F).of_iso (homologySheafShiftIso _ a n (a + n) rfl)

/-- The cohomology sheaf of a shifted Weil sheaf `F[a]` in degree `-a` is `F`. -/
noncomputable def homologySheafShiftToComplexIso (F : WeilSheaf k₀ l X) (a n : ℤ)
    (h : a + n = 0) : (homologySheaf n).obj ((WeilSheaf.toComplex.obj F)⟦a⟧) ≅ F :=
  homologySheafShiftIso _ a n 0 h ≪≫ homologySheafSingleComplexIso 0 F

end AlgebraicGeometry.WeilComplex
