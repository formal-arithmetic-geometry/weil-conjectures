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
/-! # Pullback coherence for the specified finite reduction map
Source: finite reduction of purity, Step 2 (blueprint: lem-pur-finite-positive-reduction-pullback).
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

/-- Pullback respects the specified semilinear root-power reduction, in every power.
Source: thm-pur-finite-reduction-of-purity.proof.md, Step 2, tensor associativity.
(blueprint: lem-pur-finite-positive-reduction-pullback).
Proof: first transpose the square by scalar extension/restriction and the module
inverse-image/direct-image adjunctions. At power one, the free-module adjunction
reduces the assertion to naturality of root exponentiation under the projection
of the pro-etale fibre product: pullback of u^(ℓ^(n-m)) equals the same power of
the pulled-back u. Check this equality on root presheaves; naturality of
sheafification then gives equality of the actual rootsDirect maps. The scalar
part is naturality of the coefficient quotient. The defining scalar-pullback
mate pullIso and uniqueness of adjuncts give the displayed power-one square.
At zero, the square is the unit compatibility of this monoidal mate, because
semilinear zero is the coefficient map and pull zero is the inverse unit
comparison. Induct on r. Expand semilinear and pull at r+1. The monoidal mate
compatibility moves the scalar tensorator through pullIso. Apply the induction
hypothesis and the power-one square to its two factors, then use associativity
and naturality of the tensor comparisons. This gives the displayed square,
with exactly the given pullIso, rather than an arbitrary comparison isomorphism.
No flatness assumption on the coefficient quotient enters this equality. -/
theorem sheafMap_pullback {X : Scheme.{u}} (f : X ⟶ T)
    (m n : ℕ) (hmn : m ≤ n) (r : ℕ) :
    (Mod.extendScalars (coefficientMap (quotient ℓ E m n hmn) X)).map
        (pull ℓ E T f n r) ≫ sheafMap ℓ E X m n hmn r =
      (CondensedRing.pullIso (quotient ℓ E m n hmn) f).hom.app (line ℓ E T n r) ≫
        (CondensedRing.upperStar (twistFiniteRing ℓ E m) f).map
          (sheafMap ℓ E T m n hmn r) ≫ pull ℓ E T f m r := by
  sorry

end AlgebraicGeometry.ProEtale.FinitePositiveReduction
