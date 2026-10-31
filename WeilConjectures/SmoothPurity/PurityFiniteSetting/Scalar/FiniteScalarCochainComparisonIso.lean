/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars

/-! # Invertibility of the native scalar cochain tensor comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w uA vA uB vB wA wB
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Functor.leftAdjoint Adjunction.ofIsRightAdjoint
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

/-- The actual ordinary scalar cochain comparison is invertible for all complexes.
Source: thm-pur-finite-reduction-of-purity, proof Step 2; Stacks 07A4 and 0FPT.
(blueprint: lem-pur-finite-scalar-cochain-comparison-invertible).
Proof: ordinary sheaf scalar extension is strong monoidal and is a left adjoint,
so preserves the sums defining the cochain tensor. The native mapped oplax tensor
natural transformation is an isomorphism; evaluate it at the two complexes. -/
theorem finiteScalarCochainComparison_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (C D : CochainComplex (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) ℤ) :
    IsIso (finiteTensorCochainComparison φ T C D) := by
  unfold finiteTensorCochainComparison
  infer_instance

end WeilConjectures.PurityFiniteSetting
