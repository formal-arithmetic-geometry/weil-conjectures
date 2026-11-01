/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Support.SupportScalarProjectionCoordinates
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarProperProjectionPresentation
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportScalarTensor
public import WeilConjectures.AlgebraicGeometry.Proper.ProperScalarCounitSquare

/-! # Canonical scalar mate intermediate arrow -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The fixed intrinsic arrow used between canonical mate normalization and endpoint transport.
Source: Stacks Tags 07A4 and 07A6 (blueprint: helper-proper-scalar-canonical-mate).
-/
noncomputable def canonicalScalarProjectionArrow
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (P : DerivedCategory
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Arrow (DerivedCategory
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) := by
  let aZ := Classical.choice (PurCompactSupport.tensorModel_exists Z (proEtaleConstantRing Z A))
  let aY := Classical.choice (PurCompactSupport.tensorModel_exists Y (proEtaleConstantRing Y A))
  let Q := ((constantSheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((ModuleCat.restrictScalars.{u + 1} φ.ulift).obj
          (ModuleCat.of (ULift.{u + 1} B) (ULift.{u + 1} B)))))
  exact Arrow.mk (((sfIntrinsicDerivedEquivalence Y A).inverse).map
    (finiteScalarProperProjection A g aZ aY
      ((sfIntrinsicDerivedEquivalence Z A).functor.obj P)
      ((sfIntrinsicDerivedEquivalence Y A).functor.obj Q)))

/-- The restricted scalar mate of the old coordinate presentation, taken for the
normalized scalar adjunctions `D_T ⊣ V_T`, is the realized native counit transpose `γ`.
This identifies the old finite consumer with the explicit counit-transpose presentation
of `lem-exc-proper-scalar-projection-normalization`.
Source: Stacks Tags 07A4 and 07A6 (blueprint: helper-proper-scalar-canonical-mate).

Proof: the restriction square of the coordinate presentation and the balanced
scalar/pullback comparison `λ` defining `γ` are conjugate: `λ` is the inverse mate of
the exact restriction comparison under `D_T ⊣ V_T`. Taking the scalar mate of the
restriction square therefore gives the geometric transpose of `D_Z(ε) ∘ λ`, which is
`γ`; restriction of scalars and `E_Y⁻¹` are applied to both sides. -/
theorem properScalarMate_canonical_mate_arrowIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (P : DerivedCategory
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Nonempty (properScalarMateArrow φ g
      (ProEtale.directImageScalarExtension φ Z) (ProEtale.directImageScalarExtension φ Y)
      (ProEtale.directImageScalarAdjunction φ Z) (ProEtale.directImageScalarAdjunction φ Y)
      P ≅
      Arrow.mk (((proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Y A).inverse).map
        ((ProEtale.directImageScalarComparison φ g).app
          ((sfIntrinsicDerivedEquivalence Z A).functor.obj P)))) := by
  sorry

end WeilConjectures
