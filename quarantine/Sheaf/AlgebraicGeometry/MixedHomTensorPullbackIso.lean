/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
import all Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso
import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorMonoidalRealization
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KFlatTensorProduct
import Sheaf.Algebra.Homology.KFlatPullback

/-! # Normalized pullback tensor isomorphism
Source: Stacks Project, Tags 079U and 0B6I.
(blueprint: lem-sc-mixed-hom-tensor-pullback-iso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
noncomputable section
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The canonical pullback tensor comparison with independent localization universes.
Proof: take the canonical comparison normalized to SingleComplexBaseChange.counit.
On K-flat representatives, tensor, pullback, localization tensor maps and the shared
left-derived counits are invertible. The canonical coordinate equation thus makes
its components invertible. K-flat resolutions and naturality transport invertibility
to arbitrary objects. Package these components as a natural isomorphism.
Source: Stacks Tags 079U and 0B6I
(blueprint: lem-sc-mixed-hom-tensor-pullback-iso). -/
theorem exists_mixedHomTensorPullbackIso {T S : Scheme.{u}} (h : T ⟶ S) :
    ∃ t : tensor (schemeDerivedCategory S) ⋙ derivedPullback h ≅
      (derivedPullback h).prod (derivedPullback h) ⋙ tensor (schemeDerivedCategory T),
      IsCanonicalPullbackTensorComparison h (fun K L ↦ t.hom.app (K, L)) := by
  obtain ⟨τ, hτ⟩ := exists_canonicalPullbackTensorComparison h
  let c : tensor (schemeDerivedCategory S) ⋙ derivedPullback h ⟶
      (derivedPullback h).prod (derivedPullback h) ⋙ tensor (schemeDerivedCategory T) :=
    { app := fun Z ↦ τ Z.1 Z.2
      naturality := fun Z Z' a ↦ hτ.2 Z.1 Z'.1 Z.2 Z'.2 a.1 a.2 }
  obtain ⟨m, hm⟩ := canonicalPullbackTensor_monoidal_realization h τ hτ
  have (Z : schemeDerivedCategory S × schemeDerivedCategory S) : IsIso (c.app Z) := by
    change IsIso (τ Z.1 Z.2)
    rw [← hm Z.1 Z.2]
    infer_instance
  exact ⟨NatIso.ofComponents (fun Z ↦ asIso (c.app Z))
    (fun a ↦ c.naturality a), hτ⟩

/-- The pullback tensorator normalized to the shared derived counit.
Source: Stacks Tag 079U. -/
def mixedHomTensorPullbackIso {T S : Scheme.{u}} (h : T ⟶ S) :
    tensor (schemeDerivedCategory S) ⋙ derivedPullback h ≅
      (derivedPullback h).prod (derivedPullback h) ⋙ tensor (schemeDerivedCategory T) :=
  Classical.choose (exists_mixedHomTensorPullbackIso h)

end AlgebraicGeometry
