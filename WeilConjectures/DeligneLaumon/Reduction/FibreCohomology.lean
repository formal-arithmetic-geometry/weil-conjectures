/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk

/-!
# Higher direct images over a base quasi-finite over `k₀`

Let `f : X ⟶ Y` be a separated morphism of finite type of `k₀`-schemes and let `t : T ⟶ Y` be a
morphism from a `k₀`-scheme quasi-finite over `k₀` (for instance the spectrum of the residue
field at a closed point of `Y`), with fibre product `X_T = X ×_Y T`. Then

`H_c^0(T, t^* Rⁱf₀!F) ≅ H_c^i(X_T, F|_{X_T})`

as Frobenius modules: compact support base change identifies `t^* Rf₀!F` with `Rf_T₀!(F|_{X_T})`,
composition identifies `R(X_T ⟶ Spec k₀)₀!` with `R(T ⟶ Spec k₀)₀! ∘ Rf_T₀!`, and the direct image
with compact support along the quasi-finite `T ⟶ Spec k₀` is exact, so it commutes with the
cohomology sheaves.

## Main statements

- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_fiber`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {X Y X' T : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [X'.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))]
  {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  {f' : X' ⟶ T} [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f'] [LocallyOfFiniteType f']
  [QuasiCompact f'] [IsSeparated (T ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))] [LocallyQuasiFinite (T ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X' ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X' ↘ Spec (CommRingCat.of k₀))]
  {g : X' ⟶ X} [g.IsOver (Spec (CommRingCat.of k₀))] {t : T ⟶ Y}
  [t.IsOver (Spec (CommRingCat.of k₀))]

/-- **Compactly supported cohomology of a fibre over a quasi-finite base.** For a cartesian square
`X' = X ×_Y T` of `k₀`-schemes with `f : X ⟶ Y` separated of finite type and `T` quasi-finite over
`k₀`, `H_c^0(T, t^* Rⁱf₀!F) ≅ H_c^i(X', g^*F)` as Frobenius modules (blueprint:
`lem-zl-relative-curve-punctual`, the identification of the stalks of `Rⁱh₀!F` with the
compactly supported cohomology of the fibres by compact support base change). -/
theorem WeilSheaf.nonempty_equiv_compactlySupportedCohomology_fiber
    (hH : IsPullback g f' f t) (F : WeilSheaf k₀ l X) (i : ℕ) :
    Nonempty ((((WeilSheaf.upperStar t).obj ((WeilSheaf.higherLowerShriek k₀ l f i).obj
      F)).compactlySupportedCohomology 0).Equiv
        (((WeilSheaf.upperStar g).obj F).compactlySupportedCohomology i)) := by
  sorry

end AlgebraicGeometry
