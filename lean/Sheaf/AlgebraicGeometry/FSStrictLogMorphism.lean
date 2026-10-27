/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup

/-!
# Strictness and identity for fs log morphisms

Source: ILO VI 1.1, VIII 3.3.8--3.3.9
(blueprint: def-per-strict-log-morphism).

These definitions are shared by log smoothness and fan charts. They are moved
verbatim from `LogFanChartBlowup`, which imports this module for legacy callers.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The relation induced on characteristic stalks by a log morphism. Representatives
are compared on a pointed relative étale diagram, so this is the graph of the canonical
map, without choosing presentations of stalk elements. Source: ILO VI 1.1, VIII 3.3.8
(blueprint: lem-trf-log-fan-chart-blowup). -/
def EtaleLogHom.CharacteristicRelation {Y X : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom Y X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ Y.scheme)
    (a : X.logStructure.characteristic (t ≫ f.base))
    (b : Y.logStructure.characteristic t) : Prop :=
  ∃ (W : X.scheme.Etale) (V : Y.scheme.Etale)
    (w : (Scheme.pointSmallEtale (t ≫ f.base)).fiber.obj W)
    (v : (Scheme.pointSmallEtale t).fiber.obj V)
    (k : V.left ⟶ W.left) (hk : k ≫ W.hom = V.hom ≫ f.base)
    (s : X.logStructure.monoidSheaf.obj.obj (op W)),
    v.left ≫ k = w.left ∧
      Associates.mk (X.logStructure.toEtalePrelogStructure.germ (t ≫ f.base) W w s) = a ∧
      Associates.mk (Y.logStructure.toEtalePrelogStructure.germ t V v
        (f.sectionMap W V k hk s)) = b

/-- Strictness is the canonical characteristic-stalk isomorphism criterion for pullback
log structures. Normalization by the graph excludes an arbitrary isomorphism.
Source: ILO VI 1.1, VIII 3.3.8 (blueprint: lem-trf-log-fan-chart-blowup). -/
def EtaleLogHom.IsStrict {Y X : FineSaturatedLogScheme.{u}} (f : EtaleLogHom Y X) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y.scheme),
    ∃ e : X.logStructure.characteristic (t ≫ f.base) ≃* Y.logStructure.characteristic t,
      ∀ a b, f.CharacteristicRelation t a b ↔ e a = b

/-- The identity log morphism, specified on all relative test sections. Source: ILO
VI 1.1 and VIII 3.3.9 (blueprint: lem-trf-log-fan-chart-blowup). -/
def EtaleLogHom.IsIdentity {X : FineSaturatedLogScheme.{u}} (f : EtaleLogHom X X) : Prop :=
  f.base = 𝟙 X.scheme ∧
    ∀ (W V : X.scheme.Etale) (k : V.left ⟶ W.left)
      (hk : k ≫ W.hom = V.hom ≫ f.base) (h : k ≫ W.hom = V.hom),
      f.sectionMap W V k hk =
        (X.logStructure.monoidSheaf.obj.map
          (MorphismProperty.Over.homMk k h : V ⟶ W).op).hom

end AlgebraicGeometry
