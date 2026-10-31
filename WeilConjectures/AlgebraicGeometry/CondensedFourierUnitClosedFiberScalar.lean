/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import Mathlib.FieldTheory.IsAlgClosed.Basic

public import WeilConjectures.AlgebraicGeometry.NativeProperScalarMateData

/-! Actual E-to-Qbar scalar comparisons at the zero-fibre endpoints. -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Scalar-extension comparisons for the two endpoints of the E zero-fibre formula.

Source: latest blueprint, lem-fd-first-formula.proof.md, coefficient paragraph;
sk-prop-scalar-six and the signed Tate coefficient compatibility.

Proof in words. Use the actual ordinary derived scalar-extension functor E → Qbar.
For the source, commute it past closed direct image and ordinary inverse image using
the scalar-six exchanges. Expand the transform and commute it with compact-support
image, tensor product and shift. Extension of the unit is the Qbar unit. Finite-etale
image exchange and naturality for translations carry the E AS character idempotent to
the idempotent of the induced Qbar character, identifying the two kernel summands.
For the target, use the closed-image, unit, tensor and shift comparisons, together
with coefficient extension of the actual signed Tate line. Negative-line compatibility
uses its evaluation normalization and does not choose a trivialization. The exchanges
apply to these lisse finite-Tor inputs and their bounded-constructible direct images.
The finite-or-algebraically-closed hypothesis on k supplies the finite base-field
cohomological dimension needed by scalar-six: finite fields have ℓ-cd at most one and
algebraically closed fields have ℓ-cd zero. Thus no extra hypothesis on k is added.
Neither comparison uses an isomorphism between the E endpoints or computes the
compact-support trace.

(blueprint: lem-fd-unit-closed-fiber-scalar)
-/
theorem first_formula_unit_closed_fiber_scalar
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ), ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    (k : Type u) [Field k] [Algebra k₀ k] (hk : Finite k ∨ IsAlgClosed k)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)))) :
  Nonempty ((WeilConjectures.LocallyFiniteAdicCompactSupport.nativeScalarClosureDerived
      (AffineSpace PUnit (Spec (.of k))) ℓ E).obj
    ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
    ((CondensedRing.upperStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).leftDerivedFunctor.obj
      ((condensedFieldFourierTransform (Profinite.continuousMapRingObj E.1) k₀ k
        ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) c).obj
      ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (AffineSpace PUnit
        (Spec (.of k))))))))) ≅
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).leftDerivedFunctor.obj
      ((condensedFieldFourierTransform (Profinite.padicAlgClRingObj ℓ) k₀ k
        ((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar
        (E.1.subtype.toMonoidHom.compAddChar ψ)) c).obj
      ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (AffineSpace PUnit (Spec
        (.of k))))))))) ∧
  Nonempty ((WeilConjectures.LocallyFiniteAdicCompactSupport.nativeScalarClosureDerived
      (AffineSpace PUnit (Spec (.of k))) ℓ E).obj
    ((shiftFunctor _ (-1 : ℤ)).obj
      (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ (spRationalTwist (AffineSpace
        PUnit (Spec (.of k))) ℓ E)
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (Spec (.of k))))))
        (-1))) ≅
    (shiftFunctor _ (-1 : ℤ)).obj
      (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ (spQbarTwist (AffineSpace
        PUnit (Spec (.of k))) ℓ)
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))))))
        (-1))) := by
  sorry

end AlgebraicGeometry.ProEtale
