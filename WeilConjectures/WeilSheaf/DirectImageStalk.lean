/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.StalkFunctor

/-!
# Stalks of the direct image along an open immersion at points of the open

Let `j : U₀ ⟶ X₀` be a quasi-compact open immersion of `k₀`-schemes locally of finite type and
`F` a Weil sheaf on `U₀`. The counit `j^* j_* F ⟶ F` is an isomorphism, so at a closed point `y`
of `U₀` the stalk of `j_* F` at `j y` is the stalk of `F` at `y`, with the same local Frobenius.

## Main statements

- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_directImage`: the stalk of `j_* F` at a
  point of `U₀`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The direct image along an open immersion does not change the stalks on the open.** For a
quasi-compact open immersion `j : U₀ ⟶ X₀` of `k₀`-schemes locally of finite type, a Weil sheaf
`F` on `U₀` and a closed point `y` of `U₀`, the stalk of `j_* F` at `j y` is the stalk of `F`
at `y`, Frobenius-equivariantly: the counit `j^* j_* F ⟶ F` is an isomorphism. -/
theorem nonempty_equiv_stalk_directImage {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) (y : U.finitePoints) (x : X.finitePoints) (hxy : j.base y.1 = x.1) :
    Nonempty ((((directImage j).obj F).stalk x).Equiv (F.stalk y)) :=
  sorry

end AlgebraicGeometry.WeilSheaf
