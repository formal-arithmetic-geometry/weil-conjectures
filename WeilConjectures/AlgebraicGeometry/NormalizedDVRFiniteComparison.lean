/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleMilnor
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! Canonical normalized-tower effectivity: a step of the current coefficient-fiber proof. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The scalar adjoint of each actual Roos projection is invertible.
Source: latest blueprint, lem-coef-normalized-dvr-effectivity.proof.md, paragraphs 1--4
(blueprint: lem-coef-sp-dvr-finite-comparison).

Proof: fix exponent n+1 and restrict to the cofinal tail m >= n. Resolve the smaller
quotient by the two-term free integral complex. After tensoring with the m-th quotient,
the augmentation fiber is the smaller quotient shifted by one; its transition from
m' to m is multiplication by ell^(m'-m). Tensor these compatible coefficient triangles
with the original strict tower. Its actual normalization maps identify the right tower
with the constant n-th level and the left tower with that level shifted, with transitions
multiplied by ell. The product shift on the left has (n+1)-st power zero; the finite
geometric sum inverts one minus shift, so its Roos fiber vanishes. The constant tower
has its diagonal Roos limit, by successive subtraction. The two-term free resolution
commutes with products and fibers, identifying the middle limit with the derived finite
reduction of spDVRLimit. Track its augmentation: it is the scalar adjoint of the original
Roos projection, with precisely the restriction composition and exact localization
factors in spDVRFiniteComparison. Exact faithful scalar restriction reflects this
isomorphism in the finite coefficient derived category. No bounds or constructibility
are used; zero complexes and the empty scheme give the zero-object isomorphism. -/
theorem normalized_dvr_finite_comparison
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (hP : IsSpNormalizedTower l E T D ((spTowerLocalization l E T D).obj P)) :
    ∀ n : ℕ, IsIso (spDVRFiniteComparison l E T D R P n) := by
  sorry

end AlgebraicGeometry.ProEtale
