/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.Topology.DimensionSupremumLocalDimensions
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.CategoryTheory.TruncationHypercohomology
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.ProperCaseConstructibility
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Proper direct image of bounded constructible complexes

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-proper-bounded-constructible.md`,
statement and proof (blueprint: lem-fin-proper-bounded-constructible).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Proper direct image preserves ordinary bounded constructible complexes with the finite
coefficients of the smooth-base-change convention, for finite-type schemes over a field.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-fin-proper-bounded-constructible.md`
(blueprint: lem-fin-proper-bounded-constructible).

Proof: (1) Choose a cohomological support interval [a,c] for K. Properness implies finite
 type, and the target is quasi-compact. The finite-type fibre-dimension bound
(`lem-fin-finite-type-fibre-dimension-bound`) gives d bounding ordinary fibres. Base change
preserves local fibre dimensions (`lem-sc-fibre-dimension-after-base-change`), and dimension
is their supremum (`lem-weil-pbc-dimension-supremum-local-dimensions`), so d bounds geometric
fibres too, including empty fibres.
(2) The coefficient module-sheaf categories are Grothendieck abelian
(`lem-weil-pbc-ring-sheaves-grothendieck`), direct image is additive and left exact
(`lem-weil-pbc-module-direct-image-left-exact`), and enough injectives exist
(`lem-weil-pbc-module-sheaves-enough-injectives`). Choose a bounded-below K-injective
representative vanishing below a (`lem-weil-pbc-dplus-injective-representative`). Apply
`thm-sp-truncation-e2` to obtain E₂^{p,q} = Rᵖb_* H^q(K) converging to H^{p+q}(Rb_*K),
with stabilization and a finite exhaustive separated abutment filtration.
(3) Proper finiteness (`thm-fin-proper-case`) makes these entries constructible and zero
outside 0 ≤ p ≤ 2d and a ≤ q ≤ c.
(4) Kernels, cokernels and extensions preserve constructibility (`thm-constructible-serre`).
Induction on pages proves constructibility of every page and its stable entries. Induction
on the finite abutment filtration proves constructibility of every cohomology sheaf.
(5) Outside [a,c+2d] all graded pieces vanish, hence the abutment vanishes. This is exactly
the bounded-constructible predicate. -/
theorem isBoundedConstructible_rightDerivedLowerStar_of_proper
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (N : ℕ)
    {k : Type u} [Field k] {Y S : Scheme.{u}}
    (aY : Y ⟶ Spec (.of k)) (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (b : Y ⟶ S) [IsProper b] (hb : b ≫ aS = aY)
    (hY : IsSmoothBaseChangeCoefficients N Λ Y)
    (hS : IsSmoothBaseChangeCoefficients N Λ S)
    (K : DerivedCategoryModule Λ Y) (hK : DerivedCategory.isBoundedConstructible Λ Y K) :
    DerivedCategory.isBoundedConstructible Λ S
      ((rightDerivedLowerStar (ModuleCat.{u + 1} Λ) b).obj K) := by
  sorry

end AlgebraicGeometry.Etale
