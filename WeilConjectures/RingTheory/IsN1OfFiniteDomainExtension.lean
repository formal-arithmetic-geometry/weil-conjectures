/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.JapaneseDomain
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.RingTheory.Noetherian.Basic

/-!
# Descent of N-1 along finite extensions of domains

## Implementation details

The inclusion `A → B` extends to an injective map of fraction fields `K → L`, which sends the
integral closure of `A` in `K` into that of `B` in `L`. The latter is finite over `A`, so the
former is finite since `A` is Noetherian.

## References

* [Stacks, Tag 032K]
-/

@[expose] public section

universe uA uB uK uL

set_option autoImplicit false

/-- N-1 descends along a finite injective extension of domains when the smaller domain
is Noetherian. -/
theorem isN1_of_finite_domain_extension
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [IsNoetherianRing A] [Module.Finite A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (hAB : Function.Injective (algebraMap A B)) (hB : IsN1 B L) : IsN1 A K := by
  let : Algebra A L := Algebra.compHom L (algebraMap A B)
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' rfl
  let g : A →ₐ[A] L := Algebra.ofId A L
  have hg : Function.Injective g :=
    (IsFractionRing.injective B L).comp hAB
  let f : K →ₐ[A] L := IsFractionRing.liftAlgHom hg
  let : Algebra A (integralClosure B L) :=
    Algebra.compHom (integralClosure B L) (algebraMap A B)
  have : IsScalarTower A B (integralClosure B L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite B (integralClosure B L) := hB
  have : Module.Finite A (integralClosure B L) :=
    Module.Finite.trans B (integralClosure B L)
  let i : integralClosure A K →ₗ[A] integralClosure B L :=
    { toFun := fun x => ⟨f x, (x.property.map f).tower_top⟩
      map_add' := by intro x y; apply Subtype.ext; exact f.map_add x y
      map_smul' := by intro a x; apply Subtype.ext; exact f.toLinearMap.map_smul a x }
  exact Module.Finite.of_injective i fun x y h =>
    Subtype.ext (f.injective (congrArg Subtype.val h))
