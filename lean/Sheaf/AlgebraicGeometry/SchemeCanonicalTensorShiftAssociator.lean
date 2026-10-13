/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift

/-! # First-variable tensor translation and reassociation

Source: Stacks Project, Tag 06YH, total tensor localization, and the triple-totalization
calculation in lem-sc-scheme-canonical-shift-unit-associativity.
(blueprint: lem-sc-scheme-canonical-tensor-shift-associator).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- Moving a translation out of the first factor commutes with reassociation.
This concerns only the associator and the tensor-shift comparisons, without any unitors.
Source: Stacks Project, Tag 06YH, total tensor localization; the triple-totalization
step of lem-sc-scheme-canonical-shift-unit-associativity.
(blueprint: lem-sc-scheme-canonical-tensor-shift-associator).

Proof. Choose K-flat complexes representing A, K and M. For a translation by n,
the first-variable total-tensor comparison identifies the summand of bidegree
(p,q) in A[n] tensor K with the summand of bidegree (p+n,q) in (A tensor K)[n].
There is no extra scalar on this first-variable comparison. Both paths below
therefore send the summand (p,q,r) to (p+n,q,r) by the inverse associator in the
category of module sheaves. On the source A[n] tensor K tensor M, the coefficients
of d_A, d_K and d_M
are (-1)^n, (-1)^p and (-1)^(p+q). On the target triple tensor at (p+n,q,r),
the coefficients before translation are 1, (-1)^(p+n) and (-1)^(p+n+q).
Translation multiplies all three by (-1)^n, giving exactly the source
coefficients since 2*n is even, also for negative n.
Thus the paths are chain maps and agree by extensionality on the totalization
summands. Apply localization to this equality. The lax monoidal associativity
identity identifies the localized complex associators with the derived
associators after inserting the invertible K-flat tensor comparisons. The
localization shift squares identify the complex first-variable comparisons
with schemeCanonicalTensorShift. Cancel these invertible comparison maps.
Finally use essential surjectivity of K-flat localization and naturality of
all these maps in each factor to transport the equality to A, K and M.
For n=0 this is ordinary associator naturality; zero factors, including the
empty scheme, give the unique maps between zero objects. -/
theorem schemeCanonicalTensorShift_associator (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (A K M : schemeDerivedCategory X) (n : ℤ) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    ((tensorRight (K ⊗ M)).commShiftIso n).hom.app A ≫ (α_ A K M).inv⟦n⟧' =
      (α_ (A⟦n⟧) K M).inv ≫
        (((tensorRight K).commShiftIso n).hom.app A) ▷ M ≫
        ((tensorRight M).commShiftIso n).hom.app (A ⊗ K) := by sorry

end AlgebraicGeometry
