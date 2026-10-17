/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.WeilSheaf.Cohomology

/-!
# The Leray isomorphism over a finite étale `k₀`-scheme

Let `P` be a finite étale `k₀`-scheme and `f : X ⟶ P` a morphism of `k₀`-schemes. The cohomology
of `P ⊗ k̄` is concentrated in degree `0`, so the Leray spectral sequence of `X ⟶ P ⟶ Spec k₀`
degenerates: `Hⁱ(X ⊗ k̄, F) ≅ Γ(P̄, Rⁱf_* F)` Frobenius-equivariantly.

## Main statements

- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_cohomology_globalSections_higherLowerStar`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {P : Scheme.{u}} [P.Over (Spec (CommRingCat.of k₀))]
  [IsFinite (P ↘ Spec (CommRingCat.of k₀))] [Etale (P ↘ Spec (CommRingCat.of k₀))]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ P) [f.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact f] [QuasiSeparated f]
  [LocallyOfFiniteType f]

/-- **Leray over a finite étale base.** For a morphism `f : X ⟶ P` of `k₀`-schemes to a finite
étale `k₀`-scheme `P` and a Weil sheaf `F` on `X`, `Hⁱ(X ⊗ k̄, F) ≅ Γ(P̄, Rⁱf_* F)` as Frobenius
modules: `Ra_{X*} ≅ Ra_{P*} ∘ Rf_*` for the structure morphisms `a_X`, `a_P`, and the cohomology
of `P ⊗ k̄` is concentrated in degree `0`. -/
theorem nonempty_equiv_cohomology_globalSections_higherLowerStar (F : WeilSheaf k₀ l X)
    (i : ℕ) :
    Nonempty ((F.cohomology i).Equiv ((higherLowerStar f i).obj F).globalSections) :=
  sorry

end AlgebraicGeometry.WeilSheaf
