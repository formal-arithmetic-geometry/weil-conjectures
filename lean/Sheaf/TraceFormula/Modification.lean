/-
Copyright (c) 2026. All rights reserved.
-/
module

public import Sheaf.TraceFormula.SchematicallyDenseOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Modifications of schemes and generic-fibre modifications

Source: Temkin, *Stable modification of relative curves*, §1.2
(blueprint: def-trf-modification).

## Main definitions

* `AlgebraicGeometry.SchemeModification`: a proper modification with schematic density.
* `AlgebraicGeometry.EtaModification`: invertibility of its canonical generic base change.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A modification is proper and an isomorphism over a schematically dense open.
Source: Temkin, *Stable modification of relative curves*, §1.2
(blueprint: def-trf-modification). -/
structure SchemeModification {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  proper : IsProper f
  dense_open : ∃ U : Y.Opens,
    SchematicallyDenseOpen U ∧
    SchematicallyDenseOpen (f ⁻¹ᵁ U) ∧
    IsIso (f ∣_ U)

/-- A modification that is an isomorphism on the whole specified generic fibre.
The source structure map is `f ≫ y`, and the generic map is the canonical base change
of `f`, obtained from the pullback functor on the slice category.
Source: Temkin, *Stable modification of relative curves*, §1.2 and §4.2
(blueprint: def-trf-modification). -/
def EtaModification {T X Y η : Scheme.{u}} (ηMap : η ⟶ T) (f : X ⟶ Y)
    (y : Y ⟶ T) : Prop :=
  SchemeModification f ∧
    IsIso (((Over.pullback ηMap).map
      (Over.homMk f rfl : Over.mk (f ≫ y) ⟶ Over.mk y)).left)

end AlgebraicGeometry
