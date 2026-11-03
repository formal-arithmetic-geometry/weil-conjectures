/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility

/-! # Algebraic-closure coefficient change and proper direct image

Source: Weil blueprint, latest, sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit,
lem-sfb-qlbar-push-iso-proper and its proof
(blueprint: lem-sfb-qlbar-push-iso-proper).

The assertion concerns the canonical (Push) comparison at bounded-below objects
of the ordinary ambient derived category of internal pro-etale modules.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing


set_option maxHeartbeats 4000000 in
-- Applying the established bounded-below comparison may require extra elaboration heartbeats.
/-- The canonical (Push) comparison for a finite p-adic subfield included in its
algebraic closure is invertible at every bounded-below object for a proper morphism.

Source: Weil blueprint, latest, lem-sfb-qlbar-push-iso-proper and its proof
(blueprint: lem-sfb-qlbar-push-iso-proper).

Proof plan:
The bounded-below proper comparison theorem
[lem-weil-pbc-condensed-qbar-bounded-push] already proves the same
`derivedPushHom` component for an ambient derived object carrying an `IsGE` bound.
Since an object of `DerivedCategory.Plus` carries such a bound in `K.property`,
apply that theorem to `K.obj`.
-/
theorem isIso_derivedPushHom_padicAlgCl_of_boundedBelow_of_isProper
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))) :
    IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) f).app K.obj) := by
  obtain ⟨n, hn⟩ := K.property
  let _ : K.obj.IsGE n := hn
  exact isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_app_of_isGE ℓ f E K.obj n

end AlgebraicGeometry.ProEtale.CondensedRing
