/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Direct images with compact support of Weil sheaves and Weil complexes

The repository already has the étale compact-support formalism: `Rf_!` is
`AlgebraicGeometry.Etale.rightDerivedLowerShriek` and `H_c` is
`AlgebraicGeometry.Etale.compactlySupportedCohomology`, both available for every separated
quasi-compact morphism locally of finite type, the `HasCompactification` hypothesis being
discharged by the Nagata instance. What is missing is their Frobenius-equivariant form on Weil
sheaves and Weil complexes, which is what the placeholders below stand for. Their
hypotheses are exactly the triple that makes the étale `Rf_!` available. They have `sorry`
bodies; see `WeilConjectures.WeilSheaf.Defs`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.higherLowerShriek` and
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek`: the higher direct images with compact
  support `Rʳf₀!` and the total derived one `Rf₀!`.
- `AlgebraicGeometry.WeilComplex.compactlySupportedCohomology` and
  `AlgebraicGeometry.WeilSheaf.compactlySupportedCohomology`: compactly supported cohomology
  with its geometric Frobenius.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

section LowerShriek

-- The binders of the next two declarations are spelled out rather than taken from a `variable`
-- block: their bodies are placeholders, so `l` and the two `Fact` hypotheses do not occur in the
-- type and would not be included.

-- TODO(unify): sk-thm-sf-package
/-- The `r`-th higher direct image with compact support `Rʳf₀!` along a separated quasi-compact
morphism of `k₀`-schemes locally of finite type. Placeholder; see
`WeilConjectures.WeilSheaf.Defs`. -/
noncomputable def WeilSheaf.higherLowerShriek (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ)
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (r : ℕ) : WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y := sorry

-- TODO(unify): sk-thm-sf-package
/-- The total derived direct image with compact support `Rf₀!` along a separated quasi-compact
morphism of `k₀`-schemes locally of finite type. Placeholder; see
`WeilConjectures.WeilSheaf.Defs`. -/
noncomputable def WeilComplex.derivedLowerShriek (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ)
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] : WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y := sorry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

-- TODO(unify): sk-thm-sf-package
instance (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (r : ℕ) :
    (WeilSheaf.higherLowerShriek k₀ l f r).Additive := sorry

-- TODO(unify): sk-thm-sf-package
instance (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    (WeilComplex.derivedLowerShriek k₀ l f).Additive := sorry

end LowerShriek

section Cohomology

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

-- TODO(unify): sk-thm-sf-global-duality
/-- The compactly supported cohomology `H_c^r(X ⊗ k, K)` of a Weil complex, with its geometric
Frobenius. -/
noncomputable def WeilComplex.compactlySupportedCohomology (r : ℤ) (K : WeilComplex k₀ l X) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) := sorry

/-- The compactly supported cohomology `H_c^r(X ⊗ k, F)` of a Weil sheaf. -/
noncomputable def WeilSheaf.compactlySupportedCohomology (r : ℤ) (F : WeilSheaf k₀ l X) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  (WeilSheaf.toComplex.obj F).compactlySupportedCohomology r

end Cohomology

end AlgebraicGeometry
