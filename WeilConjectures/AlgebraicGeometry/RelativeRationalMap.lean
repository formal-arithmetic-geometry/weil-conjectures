/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

/-!
# Relative rational maps on fibrewise dense opens

Source: Bosch--Lutkebohmert--Raynaud, Neron Models, Section 2.5, printed pp.55--57
(blueprint: def-sfb-relative-rational-map).

The quotient uses agreement on a common fibrewise dense open. Finite intersections of
fibrewise dense opens are fibrewise dense, so this relation is already an equivalence
relation. `Quot` implements its equivalence classes without postponing any construction.
The composite predicate specifies the pullback of every representative, rather than
choosing a morphism or a representative. Its unique existence for flat maps is stated
in `relative_rational_flat_regularity`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace Scheme

variable {S X Y X' : Scheme.{u}}

/-- An open is relatively dense if its inverse image is dense in every scheme-theoretic
fibre. Source: BLR 2.5, p.55 (blueprint: def-sfb-relative-rational-map). -/
def IsFibrewiseDenseOpen (sX : X ⟶ S) (U : X.Opens) : Prop :=
  ∀ s : S, Dense ((sX.fiberι s) ⁻¹' (U : Set X))

/-- A representative of a relative rational map is a morphism over the base on a
fibrewise dense open. Source: BLR 2.5, p.55 (blueprint: def-sfb-relative-rational-map). -/
structure RelativePartialMap (sX : X ⟶ S) (sY : Y ⟶ S) where
  /-- The representative's open domain. -/
  domain : X.Opens
  /-- Density in each fibre of the structure map. -/
  dense : IsFibrewiseDenseOpen sX domain
  /-- The morphism on the open subscheme. -/
  hom : domain.toScheme ⟶ Y
  /-- The morphism respects the specified base maps. -/
  over : hom ≫ sY = domain.ι ≫ sX

/-- Representatives agree when their restrictions to a common fibrewise dense open
agree. Source: BLR 2.5, p.55 (blueprint: def-sfb-relative-rational-map). -/
def RelativePartialMap.Equiv {sX : X ⟶ S} {sY : Y ⟶ S}
    (a b : RelativePartialMap sX sY) : Prop :=
  ∃ (W : X.Opens), IsFibrewiseDenseOpen sX W ∧
    ∃ (ha : W ≤ a.domain) (hb : W ≤ b.domain),
      X.homOfLE ha ≫ a.hom = X.homOfLE hb ≫ b.hom

/-- Relative rational maps are equivalence classes of relative partial maps.
Source: BLR 2.5, p.55 (blueprint: def-sfb-relative-rational-map). -/
def RelativeRationalMap (sX : X ⟶ S) (sY : Y ⟶ S) : Type u :=
  Quot (@RelativePartialMap.Equiv _ _ _ sX sY)

/-- The class of an actual relative partial morphism.
Source: BLR 2.5, p.55 (blueprint: def-sfb-relative-rational-map). -/
def RelativePartialMap.classOf {sX : X ⟶ S} {sY : Y ⟶ S}
    (a : RelativePartialMap sX sY) : RelativeRationalMap sX sY :=
  Quot.mk _ a

/-- The maximal domain is the union of the domains of all representatives.
Source: BLR 2.5, pp.55,57 (blueprint: def-sfb-relative-rational-map). -/
def RelativeRationalMap.domain {sX : X ⟶ S} {sY : Y ⟶ S}
    (φ : RelativeRationalMap sX sY) : X.Opens :=
  sSup {U | ∃ a : RelativePartialMap sX sY, a.classOf = φ ∧ a.domain = U}

/-- A morphism represents the class precisely when its domain is fibrewise dense,
it is over the base, and its relative partial-map class is the prescribed class.
Source: BLR 2.5, p.55 (blueprint: def-sfb-relative-rational-map). -/
def RelativeRationalMap.Represents {sX : X ⟶ S} {sY : Y ⟶ S}
    (φ : RelativeRationalMap sX sY) (U : X.Opens) (f : U.toScheme ⟶ Y) : Prop :=
  ∃ (hd : IsFibrewiseDenseOpen sX U) (ho : f ≫ sY = U.ι ≫ sX),
    (RelativePartialMap.mk U hd f ho).classOf = φ

/-- A composite is characterized by pulling back every representative to its actual
inverse-image open, with the canonical restricted morphism. Existence entails density
of all these inverse images. Source: BLR 2.5 Proposition 5, p.58
(blueprint: def-sfb-relative-rational-map). -/
def RelativeRationalMap.IsComposite {sX : X ⟶ S} {sY : Y ⟶ S} {sX' : X' ⟶ S}
    (φ : RelativeRationalMap sX sY) (p : X' ⟶ X)
    (ψ : RelativeRationalMap sX' sY) : Prop :=
  ∀ a : RelativePartialMap sX sY, a.classOf = φ →
    ψ.Represents (p ⁻¹ᵁ a.domain) ((p ∣_ a.domain) ≫ a.hom)

end Scheme

end AlgebraicGeometry
