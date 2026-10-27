/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocallyFiniteAdicCompactSupportData

/-! # Independence of the normalized integral coefficient presentation -/

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
Any two normalized coefficient presentations induce the same integral map into the
native coefficient sheaf.  This is the finite-quotient uniqueness step in
Bhatt--Scholze, Lemma 6.8.2.
(blueprint: lem-sf-native-completed-coefficient-change)

Proof source: compose both maps with every finite quotient projection.  The finite
constant and residue equations force equality on each projection, and the completed
coefficient sheaf is the inverse limit of these quotients, so joint monicity gives
the equality of the original maps.
-/
theorem coefficientPresentation_integralMap_eq
    [G : NativeGeometry.{u} l]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (i : E →ₐ[Padic l] PadicAlgCl l) (T : Scheme.{u})
    (C D : CoefficientPresentation l T E i) :
    C.integralMap l T = D.integralMap l T := by
  sorry

end WeilConjectures.LocallyFiniteAdicCompactSupport
