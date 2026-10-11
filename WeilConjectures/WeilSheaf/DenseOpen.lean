/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.Constant

/-!
# Lisse sheaves and dense opens

Let `j : U ↪ X` be a dense open immersion of `k₀`-schemes, with `X` smooth over `k₀`. Since the
fundamental group of a dense open of a connected normal scheme surjects onto that of the scheme,
lisse sheaves on `X` are determined by their restriction to `U`:

- the adjunction unit `N ⟶ j̄_* j̄^* N` is an isomorphism for every lisse `ℓ`-adic sheaf `N` on
  the geometric fiber `X̄`; in particular `j̄_* ℚ̄_ℓ ≅ ℚ̄_ℓ`;
- if `X` is a smooth geometrically connected curve, the restriction `j^*` carries irreducible
  lisse Weil sheaves to irreducible lisse Weil sheaves.

Both are parts of the blueprint lemma `lem-wf-dense-open-pi1-surjective` (subsection
`sk-i-real-boundary`), stated here for Weil sheaves with `sorry`.

## Main statements

- `AlgebraicGeometry.ProEtale.isIso_adicUpperStarLowerStarAdjunction_unit_app_geometricFiberMap`:
  lisse sheaves extend uniquely across the boundary of a dense open.
- `AlgebraicGeometry.ProEtale.nonempty_adicLowerStar_unit_iso_geometricFiberMap`:
  `j̄_* ℚ̄_ℓ ≅ ℚ̄_ℓ`.
- `AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.upperStar_of_isDominant`: restriction to a
  dense open of a curve preserves irreducibility.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

namespace ProEtale

/-- *Lisse sheaves extend uniquely.* Let `j : U ↪ X` be a dense open immersion of `k₀`-schemes,
with `X` smooth over `k₀`, so that the geometric fiber `X̄` is normal and `Ū` is dense in it.
For every lisse `ℓ`-adic sheaf `N` on `X̄` the adjunction unit `N ⟶ j̄_* j̄^* N` is an
isomorphism. (blueprint: `lem-wf-dense-open-pi1-surjective`, part (3), subsection
`sk-i-real-boundary`) -/
theorem isIso_adicUpperStarLowerStarAdjunction_unit_app_geometricFiberMap
    [Smooth (X ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    [j.IsOver (Spec (CommRingCat.of k₀))]
    (N : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (hN : IsAdicLisseSheaf N) :
    IsIso ((adicUpperStarLowerStarAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app N) :=
  sorry

/-- For a dense open immersion `j : U ↪ X` of `k₀`-schemes with `X` smooth over `k₀`, the
pushforward `j̄_* ℚ̄_ℓ` of the constant sheaf of the geometric fiber `Ū` is the constant sheaf of
`X̄`: the unit `ℚ̄_ℓ ⟶ j̄_* j̄^* ℚ̄_ℓ = j̄_* ℚ̄_ℓ` is an isomorphism. -/
theorem nonempty_adicLowerStar_unit_iso_geometricFiberMap
    [Smooth (X ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    Nonempty ((Scheme.Hom.geometricFiberMap j (comp_over j _))_*ᵃ[l].obj
        (AdicSheaf.unit l (U ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≅
      AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  have := isIso_adicUpperStarLowerStarAdjunction_unit_app_geometricFiberMap (k₀ := k₀) (l := l)
    j (AdicSheaf.unit l _) (isAdicLisseSheaf_adicConstantSheaf _)
  exact ⟨(Scheme.Hom.geometricFiberMap j (comp_over j _))_*ᵃ[l].mapIso
    (adicUpperStarUnitIso l _).symm ≪≫ (asIso ((adicUpperStarLowerStarAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app _)).symm⟩

end ProEtale

namespace WeilSheaf

variable [Fact (ringChar k₀ ≠ l)]

/-- *Restriction to a dense open of a curve preserves irreducibility.* Let `X` be a smooth
geometrically connected curve over `k₀` and `j : U ↪ X` a dense open immersion. The restriction
`j^*` carries irreducible lisse Weil sheaves on `X` to irreducible lisse Weil sheaves on `U`: the
Weil group of `U` surjects onto that of `X`.
(blueprint: `lem-wf-dense-open-pi1-surjective`, part (4), subsection `sk-i-real-boundary`) -/
theorem IsIrreducibleLisse.upperStar_of_isDominant
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of k₀))]
    {M : WeilSheaf k₀ l X} (hM : M.IsIrreducibleLisse) :
    ((upperStar j).obj M).IsIrreducibleLisse :=
  sorry

end WeilSheaf

end AlgebraicGeometry
