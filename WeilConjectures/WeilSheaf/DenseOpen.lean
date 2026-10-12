/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.MiddleExtension

/-!
# Lisse sheaves and dense opens

Let `j : U ↪ X` be a dense open immersion of `k₀`-schemes, with `X` smooth over `k₀`. Since the
fundamental group of a dense open of a connected normal scheme surjects onto that of the scheme,
lisse sheaves on `X` are determined by their restriction to `U`:

- if `X` is a smooth curve, `j̄_* ℚ̄_ℓ ≅ ℚ̄_ℓ`, from the description of a lisse Weil sheaf as the
  direct image of its restriction to `U` (blueprint `lem-a1-lisse-middle-extension`);
- if `X` is a smooth geometrically connected curve, the restriction `j^*` carries irreducible
  lisse Weil sheaves to irreducible lisse Weil sheaves.

The second is part (4) of the blueprint lemma `lem-wf-dense-open-pi1-surjective` (subsection
`sk-i-real-boundary`), stated here for Weil sheaves with `sorry`.

## Main statements

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

variable [Fact (ringChar k₀ ≠ l)]

/-- For a dense quasi-compact open immersion `j : U ↪ X` of `k₀`-schemes with `X` a smooth curve
over `k₀`, the pushforward `j̄_* ℚ̄_ℓ` of the constant sheaf of the geometric fiber `Ū` is the
constant sheaf of `X̄`: the constant Weil sheaf is lisse, hence the direct image of its
restriction to `U` (`AlgebraicGeometry.WeilSheaf.IsLisse.nonempty_iso_directImage_upperStar`,
blueprint `lem-a1-lisse-middle-extension`), and the restriction of `ℚ̄_ℓ` is `ℚ̄_ℓ`. -/
theorem nonempty_adicLowerStar_unit_iso_geometricFiberMap
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    Nonempty ((Scheme.Hom.geometricFiberMap j (comp_over j _))_*ᵃ[l].obj
        (AdicSheaf.unit l (U ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≅
      AdicSheaf.unit l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  obtain ⟨e⟩ := (WeilSheaf.isLisse_adicConstant k₀ l X).nonempty_iso_directImage_upperStar j
    j.denseRange
  let E := ((WeilSheaf.objectProperty k₀ l X).ι ⋙
    Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).mapIso e
  exact ⟨(Scheme.Hom.geometricFiberMap j (comp_over j _))_*ᵃ[l].mapIso
    (adicUpperStarUnitIso l _).symm ≪≫ E.symm⟩

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
