/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit

/-! # The counit bijection for the actual integral exceptional value

Source: current blueprint prop-coef-integral-dualizing.proof.md, paragraph 2,
the degree-zero case of the shifted adjunction bijections.
(blueprint: lem-coef-integral-dualizing-native-counit-bijection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Compact support followed by the specified exceptional counit induces the ambient
Hom bijection. No completeness, finite-level comparison, or enriched adjunction is used.

Source: current blueprint prop-coef-integral-dualizing.proof.md, paragraph 2
(blueprint: lem-coef-integral-dualizing-native-counit-bijection).

Proof: the full inclusions identify ambient morphisms with morphisms in the two
bounded constructible categories. Between them use the inverse of the restricted
exceptional adjunction's Hom equivalence. The counit formula for that inverse is
F(h) followed by epsilon. Full-subcategory composition and the definition of the
restricted compact-support functor give the displayed formula, with its actual
compactification and counit. The same equivalences apply to zero inputs and empty
schemes; no faithfulness of global sections is asserted.
-/
theorem integralDualizing_native_counit_bijective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (hk : Finite k ∨ IsAlgClosed k)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (hΛ : IsNativeExceptionalCoefficient l Λ)
    (K : ConstantModelBoundedConstructible Λ X.left)
    (U : ConstantModelBoundedConstructible Λ Y.left) :
    Function.Bijective (fun h : K.obj ⟶
        ((currentExceptionalInverseImage Λ l k hk f hΛ).obj U).obj ↦
      (rightDerivedLowerShriekOfCompactification Λ (compactificationOverField f)).map h ≫
        ((currentExceptionalAdjunction Λ l k hk f hΛ).counit.app U).hom) := by
  let F := nativeConstructibleLowerShriek Λ l k (exceptionalCurrentFieldCD l k hk) f hΛ
  let G := currentExceptionalInverseImage Λ l k hk f hΛ
  let adj : F ⊣ G := currentExceptionalAdjunction Λ l k hk f hΛ
  let e := (constantModelBoundedConstructible Λ X.left).fullyFaithfulι.homEquiv.symm.trans
    ((adj.homEquiv K U).symm.trans
      (constantModelBoundedConstructible Λ Y.left).fullyFaithfulι.homEquiv)
  convert e.bijective using 1
  funext h
  change _ = ((adj.homEquiv K U).symm (ObjectProperty.homMk h)).hom
  rw [Adjunction.homEquiv_counit]
  rfl

end WeilConjectures
