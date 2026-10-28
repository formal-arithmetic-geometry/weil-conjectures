/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocallyFiniteAdicCompactSupportData

/-! # Pointwise normalized completed-to-native coefficient presentations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]

/--
For one scheme, the finite quotient realization of completed coefficients admits a
normalized coefficient presentation in the native locally finite coefficient ring.

Proof source: Bhatt--Scholze, Lemma 6.8.2 and Section 6.8. Construct the inverse-limit
identification from the finite quotient realizations, then use the finite constant and
residue equations to normalize the localization and rational inclusion.
(blueprint: lem-sf-native-completed-coefficient-presentation-at)
-/
theorem exists_native_completed_coefficient_presentation_at
    [G : NativeGeometry.{u} l]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) (T : Scheme.{u}) :
    Nonempty (CoefficientPresentation l T E i) := by
  sorry

end WeilConjectures.LocallyFiniteAdicCompactSupport
