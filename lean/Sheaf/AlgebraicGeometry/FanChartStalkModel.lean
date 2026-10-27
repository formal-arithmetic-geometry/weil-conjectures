/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.AlgebraicGeometry.StrictFanChartLocalComparison

/-!
# The ordinary stalk model of a characteristic fan chart

Source: ILO VI 3.7(a), VIII 3.1.4(iii), 3.1.10(ii), 3.3.12--3.3.13.
(blueprint: lem-trf-fan-chart-stalk-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The actual quotient-and-sheafification morphism from Zariski log sections to
characteristic sections. Source: ILO VIII 3.1.1, 3.3.12
(blueprint: lem-trf-fan-chart-local-monoid-lift). -/
noncomputable def EtaleLogStructure.zariskiSharpening {X : Scheme.{u}}
    (M : EtaleLogStructure X) : M.zariskiPresheaf ⟶ M.sharpSpace.presheaf :=
  { app := fun _ ↦ CommMonCat.ofHom Associates.mkMonoidHom
    naturality := by
      intro U V f
      ext m
      rfl } ≫
    toSheafify (Opens.grothendieckTopology X.carrier) (FineFan.sharpPresheaf M.zariskiPresheaf)

/-- The canonical quotient of the ordinary log stalk, with its characteristic identified
with the fan stalk by the given chart. Source: ILO VI 3.7(a), VIII 3.3.12
(blueprint: lem-trf-fan-chart-local-monoid-lift). -/
noncomputable def LogFanChart.stalkQuotient {X : FineSaturatedLogScheme.{u}}
    {F : FineFan.Fan.{u}} (c : LogFanChart X F) (x : X.scheme) :
    FineFan.stalk X.logStructure.zariskiPresheaf x →*
      FineFan.stalk F.space.presheaf (c.map.hom.base x) :=
  (MulEquiv.ofBijective (FineFan.stalkMap c.map x).hom
    (c.stalkBijective x)).symm.toMonoidHom.comp
      (colim.map (whiskerLeft (OpenNhds.inclusion x).op
        X.logStructure.zariskiSharpening)).hom

/-- Groupification of the canonical quotient, constructed by the group-completion
universal property. Source: ILO VI 3.7(a), exact sequence (3.a)
(blueprint: lem-trf-fan-chart-local-monoid-lift). -/
noncomputable def LogFanChart.stalkGroupQuotient {X : FineSaturatedLogScheme.{u}}
    {F : FineFan.Fan.{u}} (c : LogFanChart X F) (x : X.scheme) :
    Algebra.GrothendieckGroup (FineFan.stalk X.logStructure.zariskiPresheaf x) →*
      Algebra.GrothendieckGroup (FineFan.stalk F.space.presheaf (c.map.hom.base x)) :=
  Algebra.GrothendieckGroup.lift (Algebra.GrothendieckGroup.of.comp (c.stalkQuotient x))

/-- The fan stalk is the actual sharpening of the ordinary log stalk. The equivalence
is normalized by the quotient map, not merely an abstract monoid equivalence.

Source: ILO VI 1.6, p.70; VIII 3.1.4(iii), 3.1.10(ii), pp.98--100, 3.3.12, p.108
(blueprint: lem-trf-fan-chart-stalk-model).

Proof: Localize a fine affine fan chart at the point. The finite-generator basic open
is the open of generalizations; its germ is an isomorphism, giving the normalized
PointLocalization. Stalks commute with the unit quotient and its sheafification:
a representative of a characteristic germ lifts after shrinking, and equality means
that the representatives differ locally by a unit. Consequently the ordinary log
stalk modulo units is the sharp-space stalk. Compose with the inverse chart stalk
isomorphism to obtain e, with the displayed normalization. Choose a geometric point
above x and an fs etale chart Q there. Zariski unit extension identifies the ordinary
characteristic with Associates (Q localized at its face of units). Its injectivity
also gives integrality of the ordinary stalk. Face sharpening makes the quotient fs,
sharp and finite free after group completion. Transport these properties through e.
For trivial characteristic the basis has rank zero; no nonempty generator assumption
is used. -/
theorem fan_chart_stalk_model
    {X : FineSaturatedLogScheme.{u}} {F : FineFan.Fan.{u}}
    (c : LogFanChart X F) (x : X.scheme) :
    ∃ (L : FineFan.PointLocalization F (c.map.hom.base x))
      (e : Associates (FineFan.stalk X.logStructure.zariskiPresheaf x) ≃*
        FineFan.stalk F.space.presheaf (c.map.hom.base x)),
      (∀ m, e (Associates.mk m) = c.stalkQuotient x m) ∧
      Function.Injective
        (Algebra.GrothendieckGroup.of (M := FineFan.stalk X.logStructure.zariskiPresheaf x)) ∧
      IsFineSaturatedMonoid (FineFan.stalk F.space.presheaf (c.map.hom.base x)) ∧
      FineFan.IsSharp (FineFan.stalk F.space.presheaf (c.map.hom.base x)) ∧
      ∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ
        (Additive (Algebra.GrothendieckGroup
          (FineFan.stalk F.space.presheaf (c.map.hom.base x))))) := by
  sorry

end AlgebraicGeometry
