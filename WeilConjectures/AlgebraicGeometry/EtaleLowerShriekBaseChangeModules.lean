/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import WeilConjectures.SixFunctors.BaseChange.Etale

/-!
# Etale extension by zero commutes with base change for module sheaves

Source: Stacks Project, Etale Cohomology, Lemma 59.70.5, Tag 03S6.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The canonical base-change transformation for etale extension by zero is an isomorphism
on sheaves of constant-ring modules. Thus every component is an isomorphism, and the
inverse components form a natural transformation in the opposite direction (Stacks, Tag 03S6). -/
theorem isIso_etaleLowerShriekBaseChangeMap (Λ : Type (u + 1)) [CommRing Λ]
    {Y V X : Scheme.{u}} (f : Y ⟶ X) (j : V ⟶ X) [Etale j] :
    IsIso (etaleLowerShriekBaseChangeMap Λ f j) := by
  unfold etaleLowerShriekBaseChangeMap
  have := Etale.isIso_baseChangeMap_flip_of_isPullback (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback f j).flip
  infer_instance

end AlgebraicGeometry.Etale
