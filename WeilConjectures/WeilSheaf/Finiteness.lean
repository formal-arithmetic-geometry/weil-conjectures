/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.LowerStar
public import WeilConjectures.WeilSheaf.PoincareDuality

/-!
# Finiteness of the cohomology of Weil complexes and Frobenius

Let `X` be a separated scheme of finite type over a finite field `k₀` with algebraic closure
`k̄`, and `K` a Weil complex on `X`. Its ordinary and compactly supported cohomology groups
`Hʳ(X ⊗ k̄, K)` and `Hʳ_c(X ⊗ k̄, K)` are finite-dimensional `ℚ̄_ℓ`-vector spaces with a geometric
Frobenius automorphism (`FrobeniusModule`), vanishing outside a finite interval. If `X` is
proper over `k₀` they agree, Frobenius-equivariantly. For the constant Weil sheaf `ℚ̄_ℓ` they
vanish outside `[0, 2e]`, `e` the dimension of `X ⊗ k̄`, and if `X` is geometrically connected
then `H⁰(X ⊗ k̄, ℚ̄_ℓ)` is `ℚ̄_ℓ` with trivial Frobenius.

## Main statements

All of them are blueprint `prop-cohomological-finiteness`.

- `AlgebraicGeometry.WeilComplex.exists_subsingleton_compactlySupportedCohomology`,
  `AlgebraicGeometry.WeilComplex.exists_subsingleton_cohomology`: the cohomology vanishes
  outside a finite interval.
- `AlgebraicGeometry.WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology`: for
  `X` proper, `Hʳ_c(X ⊗ k̄, K) ≅ Hʳ(X ⊗ k̄, K)` compatibly with Frobenius (for some isomorphism,
  not yet for the canonical one).
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_adicConstant`,
  `AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant_of_isProper`: the
  cohomology of the constant Weil sheaf vanishes outside `[0, 2e]`.
- `AlgebraicGeometry.WeilSheaf.finrank_cohomology_zero_adicConstant`,
  `AlgebraicGeometry.WeilSheaf.frobenius_cohomology_zero_adicConstant`: for `X` geometrically
  connected, `H⁰(X ⊗ k̄, ℚ̄_ℓ)` is one-dimensional with trivial Frobenius.

## Implementation notes

The blueprint states the proposition for Weil complexes with coefficients in a finite
extension `E` of `ℚ_ℓ`; the Weil complexes of the repository have coefficients in `ℚ̄_ℓ`. The
finite dimensionality of the cohomology groups is part of the structure `FrobeniusModule` that
they are valued in, so it is not restated here.

The blueprint's comparison for proper `X` concerns the canonical isomorphism
`H_c^r(X ⊗ k̄, K) → Hʳ(X ⊗ k̄, K)` induced by `Ra_! ≅ Ra_*`. That isomorphism is not yet
constructed for Weil complexes, so
`AlgebraicGeometry.WeilComplex.nonempty_equiv_compactlySupportedCohomology_cohomology` only
asserts that some Frobenius-equivariant isomorphism exists.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
section Separated

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

/-- Blueprint `prop-cohomological-finiteness`: Compact-support finiteness and Frobenius.

The compactly supported cohomology `Hʳ_c(X ⊗ k̄, K)` of a Weil complex vanishes outside a finite
interval of degrees `r`. -/
theorem exists_subsingleton_compactlySupportedCohomology (K : WeilComplex k₀ l X) :
    ∃ a b : ℤ, ∀ r, r < a ∨ b < r → Subsingleton (K.compactlySupportedCohomology r).carrier :=
  sorry

/-- Blueprint `prop-cohomological-finiteness`: Compact-support finiteness and Frobenius.

The ordinary cohomology `Hʳ(X ⊗ k̄, K)` of a Weil complex vanishes outside a finite interval of
degrees `r`. -/
theorem exists_subsingleton_cohomology (K : WeilComplex k₀ l X) :
    ∃ a b : ℤ, ∀ r, r < a ∨ b < r → Subsingleton (K.cohomology r).carrier :=
  sorry

end WeilComplex

namespace WeilSheaf

variable (k₀ l X)

/-- Blueprint `prop-cohomological-finiteness`: Compact-support finiteness and Frobenius.

If the geometric fiber `X ⊗ k̄` has dimension at most `e`, the compactly supported cohomology
`Hʳ_c(X ⊗ k̄, ℚ̄_ℓ)` of the constant Weil sheaf vanishes for `r < 0` and for `r > 2e`. -/
theorem subsingleton_compactlySupportedCohomology_adicConstant (e : ℕ)
    (he : topologicalKrullDim (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≤ (e : WithBot ℕ∞))
    (r : ℤ) (hr : r < 0 ∨ 2 * (e : ℤ) < r) :
    Subsingleton ((adicConstant k₀ l X).compactlySupportedCohomology r).carrier :=
  sorry

/-- Blueprint `prop-cohomological-finiteness`: Compact-support finiteness and Frobenius.

If `X` is geometrically connected over `k₀`, then `H⁰(X ⊗ k̄, ℚ̄_ℓ)` is one-dimensional: the
constant sheaf is the lisse sheaf of the trivial representation of the fundamental group of the
connected scheme `X ⊗ k̄`, whose invariants are `ℚ̄_ℓ`. Neither properness nor smoothness is
needed. -/
theorem finrank_cohomology_zero_adicConstant
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] :
    Module.finrank (PadicAlgCl l) ((adicConstant k₀ l X).cohomology 0).carrier =
      1 :=
  sorry

/-- Blueprint `prop-cohomological-finiteness`: Compact-support finiteness and Frobenius.

If `X` is geometrically connected over `k₀`, the geometric Frobenius acts as the identity on
`H⁰(X ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ`: the Weil structure of the constant Weil sheaf is the identity on the
constants. -/
theorem frobenius_cohomology_zero_adicConstant
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] :
    ((adicConstant k₀ l X).cohomology 0).frobenius = LinearEquiv.refl _ _ :=
  sorry

end WeilSheaf

end Separated

section Proper

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

/-- Blueprint `prop-cohomological-finiteness`: Compact-support finiteness and Frobenius.

If `X` is proper over `k₀`, the compactly supported and the ordinary cohomology
`Hʳ_c(X ⊗ k̄, K)` and `Hʳ(X ⊗ k̄, K)` are isomorphic as Frobenius modules.

This is weaker than the blueprint, which asserts that the *canonical* isomorphism, induced by
`Ra_! ≅ Ra_*` for the proper `a`, is Frobenius-equivariant. The canonical isomorphism cannot be
named yet: `Ra_! ≅ Ra_*` is only available for étale sheaves
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`), not for the
pro-étale Weil complexes `AlgebraicGeometry.WeilComplex.derivedLowerShriek` and
`AlgebraicGeometry.WeilComplex.derivedLowerStar`. -/
theorem nonempty_equiv_compactlySupportedCohomology_cohomology
    (K : WeilComplex k₀ l X) (r : ℤ) :
    Nonempty ((K.compactlySupportedCohomology r).Equiv (K.cohomology r)) :=
  sorry

end WeilComplex

namespace WeilSheaf

variable (k₀ l X)

/-- Blueprint `prop-cohomological-finiteness`: Compact-support finiteness and Frobenius.

If `X` is proper over `k₀` and the geometric fiber `X ⊗ k̄` has dimension at most `e`, the
cohomology `Hʳ(X ⊗ k̄, ℚ̄_ℓ)` of the constant Weil sheaf vanishes for `r < 0` and for `r > 2e`.
For `X` smooth of pure dimension `d` the same vanishing, without properness, is
`AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant`. -/
theorem subsingleton_cohomology_adicConstant_of_isProper (e : ℕ)
    (he : topologicalKrullDim (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≤ (e : WithBot ℕ∞))
    (r : ℤ) (hr : r < 0 ∨ 2 * (e : ℤ) < r) :
    Subsingleton ((adicConstant k₀ l X).cohomology r).carrier :=
  sorry

end WeilSheaf

end Proper

end AlgebraicGeometry
