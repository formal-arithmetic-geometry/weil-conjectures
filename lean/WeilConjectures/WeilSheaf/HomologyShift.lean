/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.Weights

/-!
# Cohomology sheaves of shifted Weil complexes

The cohomology sheaves of a shifted Weil complex are those of the complex, reindexed:
`𝓗ᵃ(K[n]) ≅ 𝓗ⁿ⁺ᵃ(K)`.

## Main declarations

- `AlgebraicGeometry.WeilComplex.isZero_homologySheaf_shift`: the cohomology sheaves of `K[n]`
  vanish where those of `K` do.
- `AlgebraicGeometry.WeilSheaf.homologySheafShiftToComplexIso`: for a Weil sheaf `F`, the
  cohomology sheaf `𝓗⁻ⁿ(F[n])` is `F`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilComplex

/-- The cohomology sheaves of a shifted Weil complex vanish where those of the complex do. -/
theorem isZero_homologySheaf_shift {K : WeilComplex k₀ l X} {n a a' : ℤ} (h : n + a = a')
    (hK : IsZero ((homologySheaf a').obj K)) : IsZero ((homologySheaf a).obj (K⟦n⟧)) :=
  hK.of_iso (homologySheafShiftIso K n a a' h)

end WeilComplex

namespace WeilSheaf

/-- The cohomology sheaf `𝓗⁻ⁿ` of a Weil sheaf placed in degree `0` and shifted by `n` is the
sheaf itself. -/
noncomputable def homologySheafShiftToComplexIso (F : WeilSheaf k₀ l X) (n : ℤ) :
    (WeilComplex.homologySheaf (-n)).obj ((toComplex.obj F)⟦n⟧) ≅ F :=
  WeilComplex.homologySheafShiftIso _ n (-n) 0 (add_neg_cancel n) ≪≫
    toComplexCompHomologySheafIso.app F

/-- The cohomology sheaves of a Weil sheaf placed in degree `0` and shifted by `n` vanish outside
degree `-n`. -/
theorem isZero_homologySheaf_shift_toComplex (F : WeilSheaf k₀ l X) {n a : ℤ} (h : a ≠ -n) :
    IsZero ((WeilComplex.homologySheaf a).obj ((toComplex.obj F)⟦n⟧)) :=
  WeilComplex.isZero_homologySheaf_shift rfl
    (WeilComplex.isZero_homologySheaf_singleComplex (by omega) F)

end WeilSheaf

end AlgebraicGeometry
