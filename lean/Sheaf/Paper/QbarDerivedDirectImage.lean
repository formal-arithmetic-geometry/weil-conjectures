/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.AdicHeartIntrinsicFibres
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Sheaf.Paper.SfCommonStageDirectImage
public import Sheaf.Paper.IntrinsicQbarCategory

/-! # Adic derived direct image over an arbitrary field

Source: Bhatt--Scholze 6.7.2, 6.8.14(2), 6.8.15
(blueprint: def-per-qbar-derived-direct-image).
The imported module retains the finite-reduction tower and its finite-field extension.
Here its constructible right-adjoint characterization is available over an arbitrary
field, using the raw completed common-stage presentation retained by the heart theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime]
  [Fact (IsUnit (l : k))]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (X Y : PerAdic.Base k) (f : X.scheme ⟶ Y.scheme)
  [hOver : f.IsOver (Spec (.of k))] [hFinite : LocallyOfFiniteType f]

include hOver hFinite in
/-- The completed Qbar pullback has the canonical derived right adjoint.
Source: Bhatt--Scholze 6.7.2, 6.8.14(2), 6.8.15
(blueprint: def-per-qbar-derived-direct-image).
Proof: derive the finite-level module direct image by K-injective resolutions.
Apply restriction of scalars and the Roos derived limit to its reduction tower;
its reduction comparisons identify the result with completed derived direct image.
The integral finite-type direct-image constructibility theorem restricts this
adjunction to bounded constructible objects. Rational transport preserves its unit
and counit. Finite scalar extension commutes with this construction, so common-stage
descent gives the displayed adjunction with the actual completed pullback. -/
theorem qbarDerivedPullback_isLeftAdjoint :
    (pbcQbarCompletedPull l Ω f).IsLeftAdjoint := by
  sorry

/-- The arbitrary-field completed Qbar derived direct image, characterized as the right
adjoint of the canonical completed pullback. Its adjunction determines the functor up
to the unique adjunction-compatible isomorphism. Source: Bhatt--Scholze 6.8.14(2), 6.8.15
(blueprint: def-per-qbar-derived-direct-image). -/
@[irreducible] def qbarDerivedDirectImage :
    pbcQbarCategory l Ω X.scheme ⥤ pbcQbarCategory l Ω Y.scheme :=
  @Functor.rightAdjoint _ _ _ _ (pbcQbarCompletedPull l Ω f)
    (qbarDerivedPullback_isLeftAdjoint l Ω X Y f)

end AlgebraicGeometry.Scheme
