/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.SmulInvertible
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Principal

/-!
# Truncations of derived complete objects

Let `(C, J)` be an essentially small site, `R` a commutative ring and `ϖ ∈ R` a nonzerodivisor,
and assume that countable products of sheaves of `R`-modules on `(C, J)` are exact. This holds
for the pro-étale site of a scheme
(`AlgebraicGeometry.Scheme.ProEt.hasExactLimitsOfShape_discrete_moduleCat`), whose topos is
replete. Then an object of `D(J, R)` is derived complete for `(ϖ)` if and only if all its
cohomology sheaves are ([BS, Proposition 3.4.4]; Stacks, Tag 091P), so the canonical truncations
of a derived complete object are derived complete.

## Main results

- `DerivedCategory.derivedComplete_iff_homology`: `K` is derived complete if and only if each
  cohomology sheaf `Hⁿ K`, placed in degree `0`, is.
- `DerivedCategory.derivedComplete_truncLT_obj`, `DerivedCategory.derivedComplete_truncGE_obj`:
  the truncations `τ_{<a} K` and `τ_{≥a} K` of a derived complete object are derived complete.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R]
  [HasExactLimitsOfShape (Discrete ℕ) (Sheaf J (ModuleCat.{u + 1} R))]
  {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

include hϖ hI

omit [HasExactLimitsOfShape (Discrete ℕ) (Sheaf J (ModuleCat.{u + 1} R))] in
/-- Derived completeness for `(ϖ)` is the right orthogonality to the objects on which `ϖ`
acts invertibly. -/
lemma derivedComplete_iff_rightOrthogonal_smulInvertible
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    derivedComplete J I K ↔
      (CategoryTheory.smulInvertible (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
        ϖ).rightOrthogonal K :=
  derivedComplete_iff_rightOrthogonal hϖ hI K

/-- **Derived completeness is detected on cohomology sheaves**: an object `K` of `D(J, R)` is
derived complete for `(ϖ)` if and only if each cohomology sheaf `Hⁿ K`, placed in degree `0`,
is derived complete. -/
theorem derivedComplete_iff_homology (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    derivedComplete J I K ↔
      ∀ n : ℤ, derivedComplete J I ((singleFunctor _ 0).obj ((homologyFunctor _ n).obj K)) := by
  simp only [derivedComplete_iff_rightOrthogonal_smulInvertible hϖ hI]
  exact rightOrthogonal_smulInvertible_iff_singleFunctor ϖ K

/-- The truncation `τ_{<a} K` of a derived complete object is derived complete. -/
theorem derivedComplete_truncLT_obj {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (hK : derivedComplete J I K) (a : ℤ) :
    derivedComplete J I ((TStructure.t.truncLT a).obj K) := by
  rw [derivedComplete_iff_rightOrthogonal_smulInvertible hϖ hI] at hK ⊢
  exact rightOrthogonal_smulInvertible_truncLT_obj ϖ hK a

/-- The truncation `τ_{≥a} K` of a derived complete object is derived complete. -/
theorem derivedComplete_truncGE_obj {K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (hK : derivedComplete J I K) (a : ℤ) :
    derivedComplete J I ((TStructure.t.truncGE a).obj K) := by
  rw [derivedComplete_iff_rightOrthogonal_smulInvertible hϖ hI] at hK ⊢
  exact rightOrthogonal_smulInvertible_truncGE_obj ϖ hK a

end DerivedCategory
