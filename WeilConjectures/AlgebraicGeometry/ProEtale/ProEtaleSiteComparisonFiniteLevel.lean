/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# Exactness, the unit, and injective acyclicity of finite-coefficient comparison

Source: blueprint, chap-Proper-base-change, theorem-proper-base-change-classical-pro,
prop-weil-pbc-site-comparison-finite-level, statement and proof, order 1285
(blueprint: prop-weil-pbc-site-comparison-finite-level).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- For a finite discrete ring, comparison inverse image is exact, the canonical unit
is invertible on every etale module sheaf, and pulled-back injectives have zero positive
higher comparison direct images.
Source: blueprint, chap-Proper-base-change, theorem-proper-base-change-classical-pro,
prop-weil-pbc-site-comparison-finite-level, order 1285
(blueprint: prop-weil-pbc-site-comparison-finite-level).

Proof:
1. The comparison inverse image preserves finite limits and is a left adjoint, hence
preserves kernels and cokernels. Its module operations make it additive, so it is exact.
2. Restrict to an affine etale object W. Comparison pullback compatibility and the
comparison section formula for the singleton system W identify the unit on W with the
identity of F(W). The affine etale site equivalence detects isomorphisms, giving the unit.
3. Etale restriction preserves injectives. Pullback compatibility identifies the restriction
of the comparison pullback of I with comparison pullback of its restriction. The identity
W/W belongs to the ind-etale basis, so comparison injective acyclicity gives vanishing of
positive cohomology on each affine etale W.
4. The pro-etale module category is Grothendieck, hence has injective resolutions. Compute
higher direct images by applying comparison direct image to such a resolution. Direct
image evaluates the same sections on etale objects; kernels are sectionwise and cokernels
are sheafified sectionwise cokernels. The resulting cohomology sheaf is the sheafification
of section cohomology. Pro-etale restriction preserves injectives, so this section
cohomology is the cohomology in step 3. Refine local representatives by affine etale
objects: all positive-degree representatives vanish. The affine etale site equivalence
therefore gives the zero higher direct image sheaf. -/
theorem siteComparison_finiteLevel (T : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] :
    PreservesFiniteLimits (comparisonUpperStar (ModuleCat.{u + 1} Λ) T) ∧
    PreservesFiniteColimits (comparisonUpperStar (ModuleCat.{u + 1} Λ) T) ∧
    (∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsIso ((T.proEtaleSiteComparisonModules Λ).unit.app F)) ∧
    (∀ (I : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (_ : Injective I)
      (q : ℕ), 0 < q →
      IsZero (((comparisonLowerStar (ModuleCat.{u + 1} Λ) T).rightDerived q).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) T).obj I))) := by
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · intro F
    change IsIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) T).unit.app F)
    have := isIso_comparisonAdjunction_unit (ModuleCat.{u + 1} Λ) T
    infer_instance
  · intro I hI q hq
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    exact rightAcyclic_comparisonUpperStar_obj_of_injective (ModuleCat.{u + 1} Λ) T I n

end AlgebraicGeometry.ProEtale
