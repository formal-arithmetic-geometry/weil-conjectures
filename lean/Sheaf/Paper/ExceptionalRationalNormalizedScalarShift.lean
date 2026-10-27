/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.Paper.ExceptionalRationalCommonCoherence
public import Sheaf.Paper.ExceptionalIntegralAdjunctionLocalizationData

/-! # The scalar shift square after canonical rational normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
  WeilConjectures.sfIntegralConstructible WeilConjectures.sfRationalTriangulationDatum
  CategoryTheory.ScalarLocalization.category
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option backward.isDefEq.respectTransparency true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
attribute [local instance 2000] shift Shrink.instField
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (A : RingStageAssembly.{u, v} l Ω D hl (f := f))
  (P : RationalStageAssembly.{u, v} l Ω D hl A)

/-- The rational scalar comparison commutes with canonically normalized shifts.
This concerns only one finite coefficient enlargement. It asserts no shift structure,
exactness, or adjunction on the common-field pair categories.
Source: Zheng, Constructions 6.2 and 6.6; common-field exactness proof, step 2
(blueprint: lem-sf-rational-normalized-scalar-shift).

Proof: fix an enlargement i ≤ j and use the integral scalar functors supplied by A.
Their realizations identify them with the completed scalar extensions, including their
shift maps. Indeed the realizations commute with shifts, and the full integral
inclusions reflect the resulting equality. The normalized integral counit comparison
therefore commutes with the canonical scalar shifts. Precompose the desired rational
square with integral rationalization at i. The normalization hs identifies the finite
operation shifts with the localizations of the integral operation shifts. The equation
P.scalar_normalized identifies the rational comparison with the localized integral
comparison, while P.action identifies the operation on each localized integral arrow.
The scalar localization comparisons identify its two scalar sides with the canonical
rational scalar shifts. The precomposed square is consequently the localization of
the integral square. Rationalization is a localization by residue Tor, so natural
transformations out of it are faithful; cancel its invertible shift comparison to
obtain the square on all rational objects. Finally commonStageTransition_eq and
commonComparisonCast transport the scalar functors and this square to the published
stage transitions. This argument applies to every integer shift, including zero and
negative shifts, and to identity coefficient extensions. -/
theorem rational_common_normalized_scalar_shift
    (c : Compactification f)
    (s : ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
      ((rationalCommonLeft A P c).Φ i).CommShift ℤ)
    (hs : ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
      let E := commonField.{u, v} l Ω i
      letI : HasShift (C.{u, v} l Ω X (.integral E)) ℤ := shift l Ω X (.integral E)
      letI : HasShift (C.{u, v} l Ω Y (.integral E)) ℤ := shift l Ω Y (.integral E)
      letI : (A.operation c (.integral E)).F.CommShift ℤ :=
        (A.operation c (.integral E)).leftShift
      letI := integralRationalizationShift.{u, v} l Ω E X
      letI := integralRationalizationShift.{u, v} l Ω E Y
      letI : (P.operation c E).F.CommShift ℤ := s i
      (P.localization c E).q.hom.CommShift ℤ) :
    ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (h : i ≤ j),
      letI := s i
      letI := s j
      ((rationalCommonLeft A P c).β h).hom.CommShift ℤ := by sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
