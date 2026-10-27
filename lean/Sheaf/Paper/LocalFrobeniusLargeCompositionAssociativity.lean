/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Paper.LocalFrobeniusLargeCoefficients

/-! # Associativity of the specified common-stage pullback compositor

Source: Bhatt--Scholze, Remark 6.8.15; the associativity clause of the integral
pullback comparison and its normalized rational and common-stage extensions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local irreducible] WeilConjectures.commonStageDerivedPullback
  WeilConjectures.LocalFrobeniusLarge.composition
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.LocalFrobeniusLarge

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The inverse compositors identify the two ways to flatten three pullbacks.
The heterogeneous equality records precisely the associativity of the scheme maps.
Source: integralPullbackComposition, associativity clause; BS Remark 6.8.15;
lem-zl-large-transport-iterate-addition, step 1
(blueprint: lem-zl-large-composition-inverse-associativity).

Proof: take inverses in the associativity equation for integralPullbackComposition.
The intervening equality transport is the one induced by scheme associativity.
Apply the rational localization functor. In the definition of localPullbackComposition,
the object comparisons at the two internal vertices cancel; their naturality moves
the remaining comparison through the pulled-back compositor. Thus the integral
associativity equation gives the rational equation with exactly its published
object comparisons. Apply the inclusion of the representative coefficient stage.
Expanding composition cancels the internal pullbackStage comparisons in the same
way. The normalized scalar comparisons commute with integral composition, so the
result is independent of any larger representative stage. This gives the displayed
equality of the specified common-stage maps; it is an equality in the derived category,
obtained before cohomology or residue reduction. -/
theorem composition_inv_assoc
    {W X Y Z : Scheme.{u}}
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (f : W ⟶ X) (h : X ⟶ Y) (k : Y ⟶ Z)
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    HEq
      ((commonStageDerivedPullback l Ω f).map (composition l Ω h k N).inv ≫
        (composition l Ω f (h ≫ k) N).inv)
      ((composition l Ω f h ((commonStageDerivedPullback l Ω k).obj N)).inv ≫
        (composition l Ω (f ≫ h) k N).inv) := by sorry

end WeilConjectures.LocalFrobeniusLarge
