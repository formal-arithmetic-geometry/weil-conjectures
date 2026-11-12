/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions

/-!
# Exact functors and filtration closures

An exact functor `F : C ⥤ D` of abelian categories carrying objects with a property `P` to
objects with a property `Q` carries objects admitting a finite filtration with successive
quotients in `P` to objects admitting a finite filtration with successive quotients in `Q`
(`CategoryTheory.ObjectProperty.filtrationClosure.map`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.ObjectProperty

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {P : ObjectProperty C} {Q : ObjectProperty D}

/-- An exact functor carrying objects with `P` to objects with `Q` carries the filtration closure
of `P` into the filtration closure of `Q`: it carries a filtration with quotients in `P` to a
filtration with quotients in `Q`. -/
theorem filtrationClosure.map (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [Q.IsClosedUnderIsomorphisms] (hF : ∀ X, P X → Q (F.obj X))
    {X : C} (hX : P.filtrationClosure X) : Q.filtrationClosure (F.obj X) := by
  induction hX with
  | of_isZero hX => exact .of_isZero (F.map_isZero hX)
  | of_mono i _ hi ih =>
    have : Mono (F.map i) := F.map_mono i
    exact .of_mono (F.map i) ih (Q.prop_of_iso (PreservesCokernel.iso F i) (hF _ hi))

end CategoryTheory.ObjectProperty
