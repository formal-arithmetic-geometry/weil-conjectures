/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V7
-/
module

public import Sheaf.Paper.FdCoefficientComparison
public import Sheaf.Paper.FdScalarPullbackRealizationIdentification

/-! # Identification of the fixed coefficient scalar comparison

Source: trace-definition whole-tower comparison, steps 8--10; Stacks 0941 and 099N.
(blueprint: lem-fd-coefficient-scalar-completion-identification). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The fixed scalar component is ordinary coefficient transport followed by
its normalized completion map.
Source: trace-definition coefficient comparison, steps 3--4 and 8--10;
Stacks 0941 and 099N
(blueprint: lem-fd-coefficient-scalar-completion-identification).

Proof: on sheafified tensor generators the ordinary module comparison in C and
c.moduleIso is fixed by the same quotient-normalized coefficient isomorphisms.
The balanced tensor universal property identifies these maps and their inverses.
Derive that identity with the canonical cochain counits retained, using the
normalization field of c. On a flat-term K-flat representative of K, substitute
C.chi and the defining localization equation of the completion comparison.
Naturality of coefficient transport moves its comparison factors across these
maps; the ordinary tensor comparison and its inverse cancel. The result is
c.derivedIso inverse followed by coefficient transport of scalarCompletionIso.
The good-complex localization is essentially surjective, so naturality transports
this identity to K. The two ambient scalar coefficient presentations agree by
the inverse-limit projection equations; the HEq inserts only that equality.
Completeness makes chi invertible even for equal fields and ramified extensions;
no finite quotient coefficient map is inverted. The formula also holds for zero K. -/
theorem fdCoefficientScalar_completionIdentification
    (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (C : FdCoefficientComparison l Ω T)
    {E L : Padic.FiniteCoefficientFields l Ω} (e : E ≤ L)
    (c : FdScalarCoefficientTransport l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) T)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T) :
    HEq ((C.integral_scalar e).hom.app K)
      (c.derivedIso.inv.app K.obj ≫
        (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
          (scalarCompletionIso l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω e) T
            K.obj K.property.1).hom) := by sorry

end WeilConjectures
