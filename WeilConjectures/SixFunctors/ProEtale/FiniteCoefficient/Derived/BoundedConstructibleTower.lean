/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.NormalizedTower
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.BoundedConstructibleComplete

/-!
# Uniformly bounded constructible towers

Let `R` be a commutative ring with an ideal `I`, put `P_n = R ⧸ Iⁿ`, and let `T` be a scheme.
An adic tower on `T_proét` is a normalized tower `M_n ∈ D(T_proét, P_n)`
(`CategoryTheory.Sheaf.NormalizedTower`): the transition maps exhibit `M_n` as the derived base
change `M_{n+1} ⊗ᴸ_{P_{n+1}} P_n`. Following blueprint `def-weil-pbc-bounded-constructible-tower`
it is *uniformly bounded constructible* if its levels are bounded constructible with cohomology
in a common interval `[a, b]` (`AlgebraicGeometry.ProEtale.IsUniformlyBoundedConstructible`).

## Implementation notes

The blueprint phrases the uniformity through local models: one finite stratification of `T`,
pro-étale coverings of the strata, and bounded complexes `L` of finite locally constant
`A_T`-modules supported in `[a, b]` with `M_n ≅ L ⊗ᴸ P_n` locally. The coefficient sheaf `A_T`
of the integral coefficients is not available in the framework of the project, where the
derived category `D(T_proét, A)` is modelled by sheaves of modules over the discrete ring `R`
(see `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.BoundedConstructibleComplete`).
The levels are therefore required to be bounded constructible of étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleIn`, the finite-level notion of the
project) with cohomology in a common interval, which is the form in which the condition enters
the definition of `Dᵇc(T_proét, A)` (`def-weil-pbc-bounded-constructible-complete`) and the tower
preservation condition (`def-weil-pbc-tower-preservation`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {T : Scheme.{u}}

/-- The levels `M_n ∈ D(T_proét, R ⧸ Iⁿ)` of a normalized tower are bounded constructible with
cohomology in `[a, b]`. -/
def IsConstructibleInTower (a b : ℤ)
    (M : Sheaf.NormalizedTower (Scheme.ProEt.topology T) I) : Prop :=
  ∀ n : ℕ, DerivedCategory.constructibleIn (ModuleCat.{u + 1} (R ⧸ I ^ n)) T a b (M.obj n)

/-- Blueprint `def-weil-pbc-bounded-constructible-tower`: Uniformly bounded constructible tower.

An adic tower `M` on `T_proét` (a normalized tower, `CategoryTheory.Sheaf.NormalizedTower`) is
*uniformly bounded constructible* if there are integers `a, b` such that every level
`M_n ∈ D(T_proét, R ⧸ Iⁿ)` is bounded constructible with cohomology in `[a, b]`. See the
module docstring for the relation with the local models of the blueprint. -/
def IsUniformlyBoundedConstructible (M : Sheaf.NormalizedTower (Scheme.ProEt.topology T) I) :
    Prop :=
  ∃ a b : ℤ, IsConstructibleInTower a b M

lemma IsConstructibleInTower.isUniformlyBoundedConstructible {a b : ℤ}
    {M : Sheaf.NormalizedTower (Scheme.ProEt.topology T) I} (hM : IsConstructibleInTower a b M) :
    IsUniformlyBoundedConstructible M :=
  ⟨a, b, hM⟩

end AlgebraicGeometry.ProEtale
