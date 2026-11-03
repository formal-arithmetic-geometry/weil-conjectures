/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPerverseSupport

/-! # Punctual sheaves in the native constructible coefficient heart

Source: latest blueprint, thm-a1-curve-perverse-heart, opening convention.
(blueprint: def-a1-native-punctual-support).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CurvePunctual

/-- Native constructible sheaves with finite closed support, including the zero sheaf.
Source: thm-a1-curve-perverse-heart, opening definition of punctual
(blueprint: def-a1-native-punctual-support). -/
def IsPunctual (ell : ℕ) [Fact ell.Prime] (C : Scheme.{u}) :
    ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) C)) :=
  fun F ↦ IsConstructibleModuleObject
    (condensedRingObj (Profinite.padicAlgClRingObj ell) C) F ∧
    (CondensedRing.condensedModuleSupport
      (condensedRingObj (Profinite.padicAlgClRingObj ell) C) F).Finite ∧
    ∀ x ∈ CondensedRing.condensedModuleSupport
      (condensedRingObj (Profinite.padicAlgClRingObj ell) C) F, IsClosed ({x} : Set C)

/-- There is no nonzero punctual subsheaf, with monomorphisms in native module sheaves.
Source: thm-a1-curve-perverse-heart, clause (1)
(blueprint: def-a1-native-punctual-support). -/
def HasNoPunctualSubsheaf (ell : ℕ) [Fact ell.Prime] (C : Scheme.{u})
    (F : Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) C)) : Prop :=
  ∀ G, ∀ i : G ⟶ F, Mono i → IsPunctual ell C G → IsZero G

end AlgebraicGeometry.ProEtale.CurvePunctual
