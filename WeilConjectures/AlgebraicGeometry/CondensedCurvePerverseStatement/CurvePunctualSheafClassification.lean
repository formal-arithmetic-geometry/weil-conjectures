/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPerverseSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.CondensedCurvePerverse.CondensedCurvePerverseStatement
public import WeilConjectures.AlgebraicGeometry.CurvePunctual.CurvePunctualSupport
public import WeilConjectures.AlgebraicGeometry.AffineLineConventions.AffineLineConventions
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstructibleTruncations
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.CategoryTheory.Simple

/-!
# Simple sheaves with finite closed support

Source: latest blueprint, `prop-a1-curve-perverse-simples.proof.md`, classification with H^-1=0.
(blueprint: lem-a1-punctual-sheaf-classification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurvePerverseStatement

/-- Simple constructible sheaves with finite closed support come from one closed point.
Source: latest blueprint, `prop-a1-curve-perverse-simples.proof.md`, degree-zero classification.
Proof: Let Z be the reduced closed subscheme given by the finite support of G.
The open restriction off Z is zero, by the geometric-stalk criterion for
constructible sheaves. Localization identifies G with the closed direct image of
its restriction to Z. The finite reduced scheme Z is the disjoint union of its
closed points Spec k(x); clopen restriction and extension give the finite direct-sum
decomposition G = direct sum i_(x*)G_x. These operations preserve constructibility,
and the inclusion of the constructible category is exact. If G is simple, exactly
one summand is nonzero, and its residue-field sheaf E is simple by exact full
faithfulness of closed direct image. Conversely, any constructible subobject of
i_(x*)E has support in {x}; localization and the closed adjunction identify its
subobjects with those of E. Thus a simple E gives a simple constructible direct
image, and closed restriction detects its nonzeroness. The empty-support case
has G=0 and satisfies neither side.
(blueprint: lem-a1-punctual-sheaf-classification). -/
theorem punctual_sheaf_classification
    (ell : ℕ) [Fact ell.Prime]
    (C : Scheme.{u}) [TopologicalSpace.NoetherianSpace C]
    (G : CondensedCurvePerverse.Modules (Profinite.padicAlgClRingObj ell) C)
    (hG : CurvePunctual.IsPunctual ell C G) :
    Simple (⟨G, hG.1⟩ : ObjectProperty.FullSubcategory
      (IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicAlgClRingObj ell) C))) ↔
    ∃ (x : C), IsClosed ({x} : Set C) ∧
      ∃ (E : CondensedCurvePerverse.Modules (Profinite.padicAlgClRingObj ell)
        (Spec (C.residueField x)))
        (hE : IsConstructibleModuleObject
          (condensedRingObj (Profinite.padicAlgClRingObj ell) (Spec (C.residueField x))) E),
        Simple (⟨E, hE⟩ : ObjectProperty.FullSubcategory
          (IsConstructibleModuleObject
            (condensedRingObj (Profinite.padicAlgClRingObj ell) (Spec (C.residueField x))))) ∧
        Nonempty (G ≅ ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ell)
          (C.fromSpecResidueField x)).obj E)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedCurvePerverseStatement
