/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
/-! # The root-normalized scalar reduction is invertible
Source: finite reduction of purity, Step 2 (blueprint: lem-pur-finite-root-scalar-isomorphism).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.FinitePositiveReduction
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E] [Algebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E] (T : Scheme.{u})

/-- The scalar adjunct of the actual root-power map is invertible.
Source: thm-pur-finite-reduction-of-purity.proof.md, Step 2, compatible root bases.
(blueprint: lem-pur-finite-root-scalar-isomorphism).
Proof: invertibility of ℓ in every residue field makes ℓ a unit in global sections.
Choose a pro-etale cover carrying one compatible primitive-root tower. The root
sheaf at level j is identified with the constant cyclic group of order ℓ^(j+1),
and the power map from level n to m becomes reduction of these cyclic groups.
The coefficient ring at level j is annihilated by ℓ^(j+1), so its free module on
this cyclic group is canonically the regular coefficient module. On these bases
the adjunct in the statement sends b tensor (a tensor zeta_n) to b bar(a)
tensor zeta_m. It is multiplication A_m tensor_(A_n) A_n to A_m, with inverse
b mapping to b tensor 1. The scalar-extension/pullback mate carries these bases
to the stated adjunct. Thus this specific map is invertible on the cover.
Inverse image along a covering family jointly reflects isomorphisms, proving
the assertion globally. The empty scheme and equal levels are included. -/
theorem rootScalar_isIso [∀ x : T, Invertible (ℓ : T.residueField x)]
    (m n : ℕ) (hmn : m ≤ n) :
    IsIso (Mod.extendHom (coefficientMap (quotient ℓ E m n hmn) T)
      (rootMap ℓ E T m n hmn)) := by
  sorry

end AlgebraicGeometry.ProEtale.FinitePositiveReduction
