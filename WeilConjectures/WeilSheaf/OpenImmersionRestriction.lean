/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.StalkIso

/-!
# Restricting extensions along an open immersion

Let `j : U ⟶ X` be a quasi-compact open immersion of `k₀`-schemes. The restriction `j^*` of the
direct image `j_*F` and of the extension by zero `j_!F` of a Weil sheaf `F` on `U` is `F` again,
and the extension by zero has zero stalks at the closed points outside `U`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.nonempty_upperStar_extensionByZero_iso`: `j^* j_! F ≅ F`.
- `AlgebraicGeometry.WeilSheaf.nonempty_upperStar_directImage_iso`: `j^* j_* F ≅ F`.
- `AlgebraicGeometry.WeilSheaf.subsingleton_stalk_extensionByZero`: `(j_! F)_x̄ = 0` for a closed
  point `x` outside `U`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]

/-- The restriction of the extension by zero along an open immersion is the sheaf itself:
`j^* j_! F ≅ F`, compatibly with the Weil structures. -/
theorem nonempty_upperStar_extensionByZero_iso (F : WeilSheaf k₀ l U) :
    Nonempty ((upperStar j).obj ((extensionByZero j).obj F) ≅ F) :=
  sorry

/-- The restriction of the direct image along an open immersion is the sheaf itself:
`j^* j_* F ≅ F`, compatibly with the Weil structures. -/
theorem nonempty_upperStar_directImage_iso
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U) :
    Nonempty ((upperStar j).obj ((directImage j).obj F) ≅ F) :=
  sorry

/-- The extension by zero along an open immersion has zero stalks at the closed points outside
the image. -/
theorem subsingleton_stalk_extensionByZero (F : WeilSheaf k₀ l U) (x : X.finitePoints)
    (hx : x.1 ∉ Set.range j.base) :
    Subsingleton (((extensionByZero j).obj F).stalk x).carrier :=
  sorry

end AlgebraicGeometry.WeilSheaf
