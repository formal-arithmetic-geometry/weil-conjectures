/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.Paper.LocallyFiniteAdicCompactSupportData

/-! # Restricted native proper scalar mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)

/-- The native proper scalar mate becomes invertible after restriction to the
completed coefficient ring. This is the coefficient-presentation comparison,
proved by normalized finite quotient projections, localization comparison, and
bounded proper push comparison described in the parent node.
Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 5.3(1).
(blueprint: lem-sf-native-proper-scalar-mate-bounded-below-restricted).
-/
theorem native_proper_scalar_mate_bounded_below_restricted
    (l : ℕ) [Fact l.Prime] [N : NativeRings.{u} l]
    (E : Index l (PadicAlgCl l))
    (a : PurCompactSupport.Change (PurCompactSupport.completed l
      (Coefficient.{u} l (PadicAlgCl l) E)) (nativeCoefficients l))
    (ha : ∀ (T : Scheme.{u})
      (C : CoefficientPresentation l T (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E)),
      a.map T = C.integralMap l T)
    {U V : Scheme.{u}} (g : U ⟶ V) [IsProper g]
    (M : DerivedCategory (pbcModules U
      ((PurCompactSupport.completed l (Coefficient.{u} l (PadicAlgCl l) E)).ring U)))
    (hM : DerivedCategory.TStructure.t.plus M) :
    IsIso ((pbcDerivedRestrict (a.map V)).map
      ((PurCompactSupport.properComparison a g).app M)) := by
  sorry

end WeilConjectures.LocallyFiniteAdicCompactSupport
